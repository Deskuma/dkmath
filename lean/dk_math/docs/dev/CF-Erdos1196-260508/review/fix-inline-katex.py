#!/usr/bin/env python3

import argparse
import difflib
import re
import sys
from pathlib import Path

"""
# Usage:
# 差分確認
python3 fix-inline-katex.py --check break-inline-KaTeX.md

# 上書き適用
python3 fix-inline-katex.py -i break-inline-KaTeX.md
"""

MATH_CHARS = set(r"\^_=+-*/<>|,:;{}[]")
MATH_WORDS = {
    "Big",
    "Body",
    "Gap",
    "GN",
    "Tail",
    "Core",
    "Beam",
    "prime",
    "power",
    "channel",
    "log",
}
MATH_ATOMS = {
    "A",
    "I",
    "T",
    "W",
    "a",
    "d",
    "i",
    "k",
    "n",
    "p",
    "q",
    "r",
    "u",
    "v",
    "w",
    "x",
    "y",
}


def read_md(filename: Path, encoding: str = "utf-8") -> str:
    return filename.read_text(encoding=encoding)


def write_md(filename: Path, content: str, encoding: str = "utf-8") -> None:
    filename.write_text(content, encoding=encoding)


def is_escaped(text: str, index: int) -> bool:
    backslashes = 0
    i = index - 1
    while i >= 0 and text[i] == "\\":
        backslashes += 1
        i -= 1
    return backslashes % 2 == 1


def closing_backtick(text: str, start: int) -> int:
    match = re.match(r"`+", text[start:])
    if match is None:
        return -1
    ticks = match.group(0)
    return text.find(ticks, start + len(ticks))


def closing_inline_dollar(text: str, start: int) -> int:
    i = start + 1
    while i < len(text):
        if text[i] == "$" and not is_escaped(text, i):
            return i
        i += 1
    return -1


def matching_paren(text: str, start: int) -> int:
    depth = 0
    i = start
    while i < len(text):
        ch = text[i]
        if ch == "`":
            end = closing_backtick(text, i)
            if end == -1:
                return -1
            i = end + 1
            continue
        if ch == "\\" and i + 1 < len(text):
            i += 2
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def looks_like_math(expr: str) -> bool:
    stripped = expr.strip()
    if not stripped:
        return False
    if "\n" in stripped:
        return False
    if any(ch in MATH_CHARS for ch in stripped):
        return True
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", stripped):
        return stripped in MATH_ATOMS
    if ("(" in stripped or ")" in stripped) and re.search(r"[A-Za-z0-9]", stripped):
        return True
    if re.search(r"\b(?:[A-Za-z]\d|\d[A-Za-z])\b", stripped):
        return True
    if re.fullmatch(r"[A-Za-z](?:\s*,\s*[A-Za-z0-9_]+)+", stripped):
        return True
    words = set(re.findall(r"[A-Za-z][A-Za-z0-9_-]*", stripped))
    return bool(words & MATH_WORDS)


def transform_text_segment(text: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "`":
            end = closing_backtick(text, i)
            if end == -1:
                out.append(text[i:])
                break
            out.append(text[i : end + len(re.match(r"`+", text[i:]).group(0))])
            i = end + len(re.match(r"`+", text[i:]).group(0))
            continue
        if ch == "$" and not is_escaped(text, i):
            end = closing_inline_dollar(text, i)
            if end != -1:
                out.append(text[i : end + 1])
                i = end + 1
                continue
        if (
            ch == "\\"
            and i + 1 < len(text)
            and text[i + 1] == "("
            and not is_escaped(text, i)
        ):
            end = text.find(r"\)", i + 2)
            if end != -1:
                out.append(text[i : end + 2])
                i = end + 2
                continue
        if ch == "(" and not is_escaped(text, i):
            end = matching_paren(text, i)
            if end != -1:
                expr = text[i + 1 : end]
                if looks_like_math(expr):
                    out.append(r"\(")
                    out.append(expr.strip())
                    out.append(r"\)")
                    i = end + 1
                    continue
        out.append(ch)
        i += 1
    return "".join(out)


def transform_markdown(content: str) -> str:
    lines = content.splitlines(keepends=True)
    out: list[str] = []
    in_fence = False
    in_math_block = False

    for line in lines:
        stripped = line.lstrip()
        if stripped.startswith("```"):
            out.append(line)
            in_fence = not in_fence
            continue

        if not in_fence and stripped.strip() == "$$":
            out.append(line)
            in_math_block = not in_math_block
            continue

        if in_fence or in_math_block:
            out.append(line)
        else:
            out.append(transform_text_segment(line))

    return "".join(out)


def unified_diff(before: str, after: str, filename: Path) -> str:
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile=f"{filename} (before)",
            tofile=f"{filename} (after)",
        )
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fix broken Markdown inline KaTeX '(...)' notation to '\\(...\\)'."
    )
    parser.add_argument("file", type=Path, help="Markdown file to transform")
    parser.add_argument(
        "-i",
        "--in-place",
        action="store_true",
        help="rewrite the input file in place",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="write transformed Markdown to this file",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="print a unified diff and exit with 1 if changes are needed",
    )
    parser.add_argument(
        "--encoding",
        default="utf-8",
        help="file encoding, default: utf-8",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    before = read_md(args.file, args.encoding)
    after = transform_markdown(before)

    if args.check:
        if before != after:
            sys.stdout.write(unified_diff(before, after, args.file))
            return 1
        return 0

    if args.in_place and args.output is not None:
        print("--in-place and --output cannot be used together", file=sys.stderr)
        return 2

    if args.in_place:
        if before != after:
            write_md(args.file, after, args.encoding)
        return 0

    if args.output is not None:
        write_md(args.output, after, args.encoding)
        return 0

    sys.stdout.write(after)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
