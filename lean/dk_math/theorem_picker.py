#! /usr/bin/env python3
# -*- coding: utf-8 -*-

# 与えられた *.lean から def, lemma, theorem, example, instance, axiom, variable, constant の行を抽出して *.md に変換する
# def は := 以降を含む
# lemma, theorem, example, instance, axiom, variable, constant は := by まで

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional


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


DECL_PATTERN = re.compile(
    r"^(?:\s*@\[.*\]\s*)*(?:private\s+)?(?:noncomputable\s+)?(def|lemma|theorem|example|instance|axiom|variable|constant)\b"
)


def detect_keyword(line: str) -> Optional[str]:
    stripped = line.lstrip()
    m = DECL_PATTERN.match(stripped)
    return m.group(1) if m else None


def first_decl_line(lines: Iterable[str]) -> Optional[str]:
    for ln in lines:
        kw = detect_keyword(ln)
        if kw:
            return ln
    return None


def find_project_root(start: Path) -> Path:
    for cur in [start] + list(start.parents):
        if (cur / "lakefile.toml").is_file() or (cur / "lean-toolchain").is_file():
            return cur
    return start


def extract_definitions_lsp(input_file: str, output_file: str) -> None:
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
        head_line = first_decl_line(snippet.splitlines())
        kw = detect_keyword(head_line or "")
        if not kw:
            continue
        ident_match = re.search(
            r"^(?:def|lemma|theorem|example|instance|axiom|variable|constant)\s+([^\s:(]+)",
            (head_line or "").lstrip(),
        )
        ident = ident_match.group(1) if ident_match else sym.get("name", "(unknown)")
        collected.append(
            {
                "keyword": kw,
                "ident": ident,
                "snippet": snippet.rstrip() + "\n",
                "truncated": False,
                "start": rng.get("start", {}).get("line", 0),
            }
        )

    collected.sort(key=lambda x: x["start"])
    write_markdown(input_file, output_file, collected)


def extract_definitions_regex(input_file: str, output_file: str) -> None:
    with open(input_file, "r", encoding="utf-8") as f:
        text = f.read()

    def remove_comments(s: str) -> str:
        out_chars: List[str] = []
        i = 0
        n = len(s)
        block_level = 0
        while i < n:
            if i + 1 < n and s[i] == "/" and s[i + 1] == "-":
                block_level += 1
                i += 2
                continue
            if i + 1 < n and s[i] == "-" and s[i + 1] == "/" and block_level > 0:
                block_level -= 1
                i += 2
                continue
            if block_level > 0:
                i += 1
                continue
            if i + 1 < n and s[i] == "-" and s[i + 1] == "-":
                i += 2
                while i < n and s[i] != "\n":
                    i += 1
                continue
            out_chars.append(s[i])
            i += 1
        return "".join(out_chars)

    cleaned = remove_comments(text)
    lines = cleaned.splitlines(keepends=True)
    start_pat = re.compile(
        r"^(?:@[\[].*\]\s*)*(?:noncomputable\s+)?(def|lemma|theorem|example|instance|axiom|variable|constant)\s"
    )
    definitions = []
    i = 0
    nlines = len(lines)
    while i < nlines:
        line = lines[i]
        stripped_line = line.lstrip()
        m = start_pat.match(stripped_line)
        if m:
            keyword = m.group(1)
            id_m = re.search(
                r"(?:def|lemma|theorem|example|instance|axiom|variable|constant)\s+([^\s:(]+)",
                stripped_line,
            )
            ident = id_m.group(1) if id_m else "(unknown)"
            j = i
            block_lines = []
            while j < nlines:
                cur = lines[j]
                cur_stripped = cur.lstrip()
                if j != i and start_pat.match(cur_stripped):
                    break
                block_lines.append(cur)
                j += 1
            truncated = False
            if keyword in ("lemma", "theorem"):
                for k, bl in enumerate(block_lines):
                    if re.search(r":=\s*by", bl):
                        block_lines = block_lines[: k + 1]
                        truncated = True
                        break
            definitions.append(
                {
                    "keyword": keyword,
                    "ident": ident,
                    "snippet": "".join(block_lines),
                    "truncated": truncated,
                    "start": i,
                }
            )
            i = j
        else:
            i += 1

    write_markdown(input_file, output_file, definitions)


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
    # コマンドライン引数の解析
    parser = argparse.ArgumentParser(
        description="Extract definitions from Lean files to Markdown."
    )
    parser.add_argument("input", help="Input .lean file")
    parser.add_argument(
        "output",
        default="__Theorems.md",
        help="Output .md file (default: Theorems.md)",
        nargs="?",
    )
    parser.add_argument(
        "--use-lsp",
        action="store_true",
        help="Use Lean LSP (lean --server) for robust parsing",
    )
    args = parser.parse_args()
    # 入力ファイルの存在確認
    if not os.path.isfile(args.input):
        # 存在しない: エラーメッセージを表示して終了
        print(f"Error: Input file {args.input} does not exist.")
        sys.exit(1)
    try:
        if args.use_lsp:
            extract_definitions_lsp(args.input, args.output)
        else:
            extract_definitions_regex(args.input, args.output)
    except Exception as exc:
        print(
            f"[warn] LSP extraction failed ({exc}). Falling back to regex parsing...",
            file=sys.stderr,
        )
        extract_definitions_regex(args.input, args.output)


if __name__ == "__main__":
    main()
