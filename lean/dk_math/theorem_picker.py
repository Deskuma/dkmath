#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Leanファイルから定義をLean LSPを使って抜き出し、Markdownに変換

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Union


# Lean LSP クライアントの簡易実装
class LeanLspClient:
    def __init__(
        self,
        cmd: Optional[List[str]] = None,
        cwd: Optional[Union[str, Path]] = None,
    ):
        self.cmd = cmd or ["lake", "env", "lean", "--server"]
        try:
            self.proc = subprocess.Popen(
                self.cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=cwd,
            )
        except OSError as exc:
            # Provide a clear message when the Lean LSP server cannot be started,
            # for example when `lake` is not installed or not in PATH.
            raise RuntimeError(
                "Failed to start Lean LSP server. "
                "Please ensure that `lake env lean --server` is installed and "
                "available in your PATH."
            ) from exc

        # If the process exits immediately, surface a helpful error with stderr.
        return_code = self.proc.poll()
        if return_code is not None:
            stderr_output = ""
            if self.proc.stderr is not None:
                try:
                    stderr_output = self.proc.stderr.read().decode(
                        "utf-8", errors="replace"
                    )
                except Exception:
                    stderr_output = ""
            msg = (
                f"Lean LSP server exited immediately with code {return_code}. "
                f"Command: {' '.join(self.cmd)}."
            )
            if stderr_output.strip():
                msg += f" Stderr: {stderr_output.strip()}"
            raise RuntimeError(msg)
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
    raise FileNotFoundError(
        f"No Lean/Lake project root found starting from '{start}'. "
        "Expected a 'lakefile.toml' or 'lean-toolchain' in this directory or one of its parents."
    )


def shorten_by_section(snippet: str) -> Dict[str, Union[str, bool]]:
    lines = snippet.rstrip().splitlines()
    for idx, line in enumerate(lines):
        if re.search(r"\bby\b", line):
            truncated = idx < len(lines) - 1
            shortened_lines = lines[: idx + 1]
            if truncated:
                # Append " ..." to the line containing "by"
                shortened_lines[-1] = shortened_lines[-1].rstrip() + " ..."
            shortened = "\n".join(shortened_lines).rstrip() + "\n"
            return {"snippet": shortened, "truncated": truncated}
    return {"snippet": snippet, "truncated": False}


def extract_definitions(input_file: str, output_file: str, short: bool) -> None:
    with open(input_file, "r", encoding="utf-8") as f:
        text = f.read()

    file_path = Path(input_file).resolve()
    root_path = find_project_root(file_path.parent)
    file_uri = file_path.as_uri()
    root_uri = root_path.as_uri()

    client = LeanLspClient(cwd=str(root_path))
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

    # LSP SymbolKind values that might be used in Lean:
    # 5=Class, 6=Method, 7=Property, 8=Field, 9=Constructor,
    # 12=Function (theorems), 13=Variable, 14=Constant, 25=Operator
    # Note: Lean LSP may use different kinds for lemma vs theorem
    allowed_kinds = {5, 6, 7, 8, 9, 12, 13, 14, 25}

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
        if short:
            shortened = shorten_by_section(snippet)
            snippet = shortened["snippet"]
            truncated = shortened["truncated"]
        else:
            snippet = snippet.rstrip() + "\n"
            truncated = False
        collected.append(
            {
                "keyword": "decl",
                "ident": ident,
                "snippet": snippet,
                "truncated": truncated,
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
            if idx < len(definitions) - 1:
                f.write("```\n\n")
            else:
                f.write("```\n")
    print(f"Extracted {len(definitions)} definitions to {output_file}")


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
    parser.add_argument(
        "--short",
        action="store_true",
        help="Truncate after the first `by` block and replace with `...`.",
    )
    parser.add_argument(
        "--find-name",
        dest="find_name",
        help="Find and extract definitions by identifier name (static grep fallback).",
        nargs="?",
    )
    parser.add_argument(
        "--insert-ident",
        dest="insert_ident",
        help="Identifier to insert into a target file (uses static search to find snippet).",
        nargs="?",
    )
    parser.add_argument(
        "--insert-target",
        dest="insert_target",
        help="Target file path to insert into.",
        nargs="?",
    )
    parser.add_argument(
        "--insert-line",
        dest="insert_line",
        type=int,
        help="Line number to insert before (1-based).",
        nargs="?",
    )
    parser.add_argument(
        "--dry-run",
        dest="dry_run",
        action="store_true",
        help="Show unified diff instead of writing changes.",
    )
    parser.add_argument(
        "--select-index",
        dest="select_index",
        type=int,
        help="If multiple candidates found, select this zero-based index automatically.",
        nargs="?",
    )
    parser.add_argument(
        "--interactive",
        dest="interactive",
        action="store_true",
        help="When multiple candidates found, prompt interactively to select one (requires TTY).",
    )
    parser.add_argument(
        "--insert-names",
        dest="insert_names",
        help="Comma-separated list of identifiers to insert in order under the given pattern.",
        nargs="?",
    )
    parser.add_argument(
        "--insert-after-pattern",
        dest="insert_after_pattern",
        help="Insert the snippets immediately after the first line matching this pattern (regex).",
        nargs="?",
    )
    args = parser.parse_args()
    if not os.path.isfile(args.input):
        print(f"Error: Input file {args.input} does not exist.")
        sys.exit(1)
    # If --find-name was provided, run a static search for the named definition
    if args.find_name:
        try:
            root = find_project_root(Path(args.input).resolve().parent)
        except FileNotFoundError:
            # fallback for standalone/temp directories used in tests
            root = Path(args.input).resolve().parent
        defs = find_definitions_by_name(root, args.find_name)
        # Write simple markdown with found definitions
        out_path = Path(args.output)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write("# Found definitions\n\n")
            f.write(f"## {args.find_name}\n\n")
            if not defs:
                f.write("No definitions found.\n")
            for item in defs:
                f.write(f"### {item['ident']} ({item['file']})\n\n")
                f.write("```lean\n")
                f.write(item["snippet"].rstrip() + "\n")
                f.write("```\n\n")
        print(f"Found {len(defs)} definitions for {args.find_name} -> {out_path}")
    else:
        extract_definitions(args.input, args.output, args.short)

    # Batch-insert workflow: insert multiple idents in order under a pattern
    if args.insert_names and args.insert_target:
        try:
            root = find_project_root(Path(args.input).resolve().parent)
        except FileNotFoundError:
            root = Path(args.input).resolve().parent
        names = [n.strip() for n in args.insert_names.split(",") if n.strip()]
        if not names:
            print("No names provided for --insert-names")
            sys.exit(2)
        defs_list = []
        for name in names:
            defs = find_definitions_by_name(root, name)
            if not defs:
                print(f"No definitions found for {name}")
                sys.exit(2)
            # choose first match by default
            defs_list.append(defs[0])
        target = Path(args.insert_target)
        if not target.exists():
            print(f"Target file {target} not found")
            sys.exit(2)
        # find insertion line: default use provided --insert-line or pattern
        insert_line = args.insert_line
        if args.insert_after_pattern:
            pat = re.compile(args.insert_after_pattern)
            text = target.read_text(encoding="utf-8")
            lines = text.splitlines()
            found = False
            for i, L in enumerate(lines):
                if pat.search(L):
                    insert_line = i + 2  # insert after this line (1-based)
                    found = True
                    break
            if not found:
                print(f"Pattern not found: {args.insert_after_pattern}")
                sys.exit(2)
        insert_line = insert_line or 1
        # build combined snippet in the given order, ensure one blank line between items
        combined = []
        target_text = target.read_text(encoding="utf-8")
        for d in defs_list:
            name = d.get("ident")
            # skip if target already defines this ident (avoid duplicates)
            pattern = re.compile(
                rf"^(?:@[\w\[\] :]+\s*)*(def|lemma|theorem)\s+{re.escape(name)}\b", re.M
            )
            if pattern.search(target_text):
                continue
            s = d.get("snippet", "").rstrip()
            if s:
                combined.append(s)
        combined_text = "\n\n".join(combined) + "\n"
        new_contents, patch = insert_snippet_into_text(
            target.read_text(encoding="utf-8"), combined_text, insert_line
        )
        if args.dry_run:
            print(patch)
        else:
            out_path = target.with_suffix(target.suffix + ".inserted")
            out_path.write_text(new_contents, encoding="utf-8")
            print(f"Wrote inserted file to {out_path}")

    # Insert ident workflow: find snippet and insert into target file
    if args.insert_ident and args.insert_target:
        try:
            root = find_project_root(Path(args.input).resolve().parent)
        except FileNotFoundError:
            root = Path(args.input).resolve().parent
        defs = find_definitions_by_name(root, args.insert_ident)
        if not defs:
            print(f"No definitions found for {args.insert_ident}")
            sys.exit(2)
        # multiple-candidate handling: print JSON list and allow selection
        if len(defs) > 1:
            # prepare summary list
            summary = []
            for i, d in enumerate(defs):
                summary.append(
                    {
                        "index": i,
                        "file": d.get("file"),
                        "ident": d.get("ident"),
                        "preview": (
                            d.get("snippet", "").splitlines()[0]
                            if d.get("snippet")
                            else ""
                        ),
                    }
                )
            # always print JSON summary for caller
            print("Found multiple candidates:")
            print(json.dumps(summary, indent=2, ensure_ascii=False))
            chosen = None
            # if select_index provided, use it
            if args.select_index is not None:
                si = args.select_index
                if 0 <= si < len(defs):
                    chosen = defs[si]
                else:
                    print(f"--select-index {si} out of range, using first candidate")
                    chosen = defs[0]
            # interactive prompt if requested and stdin is a TTY
            elif args.interactive and sys.stdin.isatty():
                try:
                    sel = input(
                        f"Select candidate index [0-{len(defs)-1}] (enter to choose 0): "
                    )
                    if sel.strip() == "":
                        chosen = defs[0]
                    else:
                        sel_i = int(sel.strip())
                        if 0 <= sel_i < len(defs):
                            chosen = defs[sel_i]
                        else:
                            print("Invalid selection, using first candidate")
                            chosen = defs[0]
                except Exception:
                    print("Interactive selection failed, using first candidate")
                    chosen = defs[0]
            else:
                # non-interactive default: pick first
                chosen = defs[0]
        else:
            chosen = defs[0]
        target = Path(args.insert_target)
        if not target.exists():
            print(f"Target file {target} not found")
            sys.exit(2)
        snippet = chosen["snippet"]
        insert_line = args.insert_line or 1
        new_contents, patch = insert_snippet_into_text(
            target.read_text(encoding="utf-8"), snippet, insert_line
        )
        if args.dry_run:
            print(patch)
        else:
            out_path = target.with_suffix(target.suffix + ".inserted")
            out_path.write_text(new_contents, encoding="utf-8")
            print(f"Wrote inserted file to {out_path}")


def insert_snippet_into_text(orig_text: str, snippet: str, insert_line: int):
    """Return (new_text, unified_diff_str) after inserting `snippet` before `insert_line` (1-based)."""
    import difflib

    lines = orig_text.splitlines(keepends=True)
    idx = max(0, min(len(lines), insert_line - 1))
    # Build snippet lines with ensured trailing newlines
    raw_snip_lines = [l + "\n" for l in snippet.splitlines()]

    # Determine whether there's already a blank line before insertion point
    need_blank_before = True
    if idx > 0 and lines[idx - 1].strip() == "":
        need_blank_before = False

    # Determine whether there's already a blank line after insertion point
    need_blank_after = True
    if idx < len(lines) and lines[idx].strip() == "":
        need_blank_after = False

    snippet_lines = []
    if need_blank_before:
        snippet_lines.append("\n")
    snippet_lines.extend(raw_snip_lines)
    if need_blank_after:
        snippet_lines.append("\n")

    new_lines = lines[:idx] + snippet_lines + lines[idx:]
    new_text = "".join(new_lines)
    diff = difflib.unified_diff(
        lines, new_lines, fromfile="orig", tofile="new", lineterm=""
    )
    patch = "\n".join(diff)
    return new_text, patch


def find_definitions_by_name(root: Path, name: str):
    """Static search: look for definitions/lemmas/theorems named `name` under root.

    This is a simple fallback using text search; it returns a list of dicts with
    keys: file, ident, snippet.
    """
    import re

    pattern = re.compile(
        r"^(?:@[\w\[\] :]+\s*)*(def|lemma|theorem)\s+" + re.escape(name) + r"\b"
    )
    results = []
    for p in root.rglob("*.lean"):
        try:
            text = p.read_text(encoding="utf-8")
        except Exception:
            continue
        lines = text.splitlines()
        for i, line in enumerate(lines):
            if pattern.search(line):
                # extract snippet: from this line until next blank line followed by a non-indented top-level start
                start = i
                end = i + 1
                while end < len(lines):
                    # stop at a blank line followed by a top-level keyword
                    if lines[end].strip() == "":
                        # lookahead
                        if end + 1 < len(lines) and re.match(
                            r"^[a-zA-Z@]", lines[end + 1]
                        ):
                            break
                    # also stop if next line looks like another top-level declaration
                    if re.match(
                        r"^(def|lemma|theorem|structure|inductive|class)\b", lines[end]
                    ):
                        break
                    end += 1
                snippet = "\n".join(lines[start:end])
                results.append(
                    {
                        "file": str(p.relative_to(root)),
                        "ident": name,
                        "snippet": snippet,
                    }
                )
                break
    return results


if __name__ == "__main__":
    main()
