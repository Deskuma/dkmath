#!/usr/bin/env python3
import re
import sys
from pathlib import Path

BUILT_RE = re.compile(
    r"^[^\n]*\b(?:Built|Replayed)\s+([A-Za-z0-9_.]+)\s*(?:\([^)]*\))?\s*$"
)
FILE_RE = re.compile(r"^[^\n]*file:\s+([A-Za-z0-9_.]+)\s*$")


def parse_pairs(lines):
    """
    ログを上から読み、
    Built/Replayed 行の次に来る file: 行を対応づける。
    """
    pending = None
    for lineno, line in enumerate(lines, start=1):
        line = line.rstrip("\n")

        m_built = BUILT_RE.match(line)
        if m_built:
            pending = {
                "kind": "build",
                "built_module": m_built.group(1),
                "built_line": lineno,
                "built_text": line,
            }
            continue

        m_file = FILE_RE.match(line)
        if m_file and pending is not None:
            yield {
                "built_module": pending["built_module"],
                "file_module": m_file.group(1),
                "built_line": pending["built_line"],
                "file_line": lineno,
                "built_text": pending["built_text"],
                "file_text": line,
            }
            pending = None


def main():
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} BUILD_LOG", file=sys.stderr)
        sys.exit(2)

    log_path = Path(sys.argv[1])
    text = log_path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()

    mismatches = []
    for pair in parse_pairs(lines):
        if pair["built_module"] != pair["file_module"]:
            mismatches.append(pair)

    if not mismatches:
        print("OK: no mismatches found")
        sys.exit(0)

    print(f"mismatches: {len(mismatches)}")
    print()

    for x in mismatches:
        # x['built_module'] から実際のファイル名にして表示 `.` を `/` に置換して `.lean` を付ける
        file = x["built_module"].replace(".", "/") + ".lean"
        print(f"file: {file}")
        print(f"{log_path}:{x['built_line']} -> {x['built_module']}")
        print(f"{log_path}:{x['file_line']} -> {x['file_module']}")
        print("  built:", x["built_text"])
        print("  file :", x["file_text"])
        print()

    sys.exit(1)


if __name__ == "__main__":
    main()
