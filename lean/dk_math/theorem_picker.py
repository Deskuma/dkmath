#! /usr/bin/env python3
# -*- coding: utf-8 -*-

# Leanファイルから定義をLean LSPを使って抜き出し、Markdownに変換

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


# Lean LSP クライアントの簡易実装
class LeanLspClient:
    def __init__(self, cmd: Optional[List[str]] = None, cwd: Optional[str] = None):
        self.cmd = cmd or ["lake", "env", "lean", "--server"]
        self.proc = subprocess.Popen(
            self.cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=cwd,
        )
        self.next_id = 1

    def _read_message(self) -> Dict[str, Any]:
        if self.proc.stdout is None:
            raise RuntimeError("Lean server stdout is not available")
        header = b""
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise RuntimeError("Lean server closed the stream")
            if line == b"\r\n" or line == b"\n":
                break
            header += line
        content_length = 0
        for hline in header.split(b"\r\n"):
            if hline.lower().startswith(b"content-length:"):
                try:
                    content_length = int(hline.split(b":")[1].strip())
                except ValueError as exc:
                    raise RuntimeError("Invalid Content-Length header") from exc
        if content_length <= 0:
            raise RuntimeError("Content-Length missing or zero")
        body = self.proc.stdout.read(content_length)
        if body is None:
            raise RuntimeError("Failed to read response body")
        return json.loads(body.decode("utf-8"))

    def _send_payload(self, payload: Dict[str, Any]) -> None:
        if self.proc.stdin is None:
            raise RuntimeError("Lean server stdin is not available")
        data = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode(
            "utf-8"
        )
        header = f"Content-Length: {len(data)}\r\n\r\n".encode("ascii")
        self.proc.stdin.write(header + data)
        self.proc.stdin.flush()

    def request(self, method: str, params: Dict[str, Any]) -> Dict[str, Any]:
        cur_id = self.next_id
        self.next_id += 1
        self._send_payload(
            {"jsonrpc": "2.0", "id": cur_id, "method": method, "params": params}
        )
        while True:
            msg = self._read_message()
            # respond to server-initiated requests to keep the session flowing
            if msg.get("id") is not None and msg.get("method") is not None:
                try:
                    self._send_payload(
                        {"jsonrpc": "2.0", "id": msg.get("id"), "result": None}
                    )
                except Exception:
                    pass
                continue
            if msg.get("id") == cur_id:
                return msg
            # notifications or unrelated responses are ignored

    def notify(self, method: str, params: Dict[str, Any]) -> None:
        self._send_payload({"jsonrpc": "2.0", "method": method, "params": params})

    def close(self) -> None:
        try:
            _ = self.request("shutdown", {})
        except Exception:
            pass
        try:
            self.notify("exit", {})
        except Exception:
            pass
        try:
            if self.proc.stdin:
                self.proc.stdin.close()
            if self.proc.stdout:
                self.proc.stdout.close()
            if self.proc.stderr:
                self.proc.stderr.close()
        finally:
            self.proc.terminate()


def find_project_root(start: Path) -> Path:
    for cur in [start] + list(start.parents):
        if (cur / "lakefile.toml").is_file() or (cur / "lean-toolchain").is_file():
            return cur
    return start


def extract_definitions(input_file: str, output_file: str) -> None:
    with open(input_file, "r", encoding="utf-8") as f:
        text = f.read()

    file_path = Path(input_file).resolve()
    root_path = find_project_root(file_path.parent)
    file_uri = file_path.as_uri()
    root_uri = root_path.as_uri()

    client = LeanLspClient(cwd=root_path)
    try:
        _ = client.request(
            "initialize",
            {
                "processId": None,
                "rootUri": root_uri,
                "capabilities": {},
                "trace": "off",
            },
        )
        client.notify("initialized", {})
        client.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": file_uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": text,
                }
            },
        )
        symbols_res = client.request(
            "textDocument/documentSymbol", {"textDocument": {"uri": file_uri}}
        )
    finally:
        client.close()

    symbols = symbols_res.get("result", []) if symbols_res else []

    def flatten(symbol_list: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        for s in symbol_list:
            out.append(s)
            if "children" in s and isinstance(s["children"], list):
                out.extend(flatten(s["children"]))
        return out

    flat_symbols = flatten(symbols) if isinstance(symbols, list) else []

    allowed_kinds = {5, 6, 12, 13, 14, 25}

    lines = text.splitlines(keepends=True)
    line_offsets: List[int] = []
    offset = 0
    for ln in lines:
        line_offsets.append(offset)
        offset += len(ln)

    def to_offset(line_no: int, ch: int) -> int:
        if line_no >= len(line_offsets):
            return len(text)
        return line_offsets[line_no] + ch

    def slice_by_range(rng: Dict[str, Dict[str, int]]) -> str:
        start = rng.get("start", {})
        end = rng.get("end", {})
        s_off = to_offset(start.get("line", 0), start.get("character", 0))
        e_off = to_offset(end.get("line", 0), end.get("character", 0))
        return text[s_off:e_off]

    collected = []
    for sym in flat_symbols:
        rng = sym.get("range")
        if not isinstance(rng, dict):
            continue
        if sym.get("kind") not in allowed_kinds:
            continue
        snippet = slice_by_range(rng)
        ident = sym.get("name", "(unknown)")
        collected.append(
            {
                "keyword": "decl",
                "ident": ident,
                "snippet": snippet.rstrip() + "\n",
                "truncated": False,
                "start": rng.get("start", {}).get("line", 0),
            }
        )

    collected.sort(key=lambda x: x["start"])
    write_markdown(input_file, output_file, collected)


def write_markdown(
    input_file: str, output_file: str, definitions: List[Dict[str, Any]]
) -> None:
    with open(output_file, "w", encoding="utf-8") as f:
        f.write("\n")
        f.write("# Theorems\n\n")
        f.write(f"## {os.path.basename(input_file)}\n\n")
        for idx, item in enumerate(definitions):
            f.write(f"### {item['ident']}\n\n")
            f.write("```lean\n")
            f.write(item["snippet"].rstrip() + "\n")
            if item.get("truncated"):
                f.write("  ...\n")
            if idx < len(definitions) - 1:
                f.write("```\n\n")
            else:
                f.write("```\n")
    print(f"Extracted {len(definitions)} definitions to {output_file}")
    return


def main():
    parser = argparse.ArgumentParser(
        description="Extract definitions from Lean files to Markdown using Lean LSP."
    )
    parser.add_argument("input", help="Input .lean file")
    parser.add_argument(
        "output",
        default="__Theorems.md",
        help="Output .md file (default: __Theorems.md)",
        nargs="?",
    )
    args = parser.parse_args()
    if not os.path.isfile(args.input):
        print(f"Error: Input file {args.input} does not exist.")
        sys.exit(1)
    extract_definitions(args.input, args.output)


if __name__ == "__main__":
    main()
