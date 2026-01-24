#! /usr/bin/env python3
# -*- coding: utf-8 -*-

# 与えられた *.lean から def, lemma, theorem, example, instance, axiom, variable, constant の行を抽出して *.md に変換する
# def は := 以降を含む
# lemma, theorem, example, instance, axiom, variable, constant は := by まで

import argparse
import os
import re
import sys
from typing import List, Tuple


# 定義抽出関数
def extract_definitions(input_file: str, output_file: str) -> None:
    """Extract definitions from a Lean file and write them to a Markdown file."""
    # 入力ファイルの読み込み
    with open(input_file, "r", encoding="utf-8") as f:
        text = f.read()

    # コメント（行コメント "--" とネスト可能なブロックコメント "/- ... -/"）を除去する
    def remove_comments(s: str) -> str:
        """Remove comments from Lean source code."""
        out_chars: List[str] = []
        i = 0
        n = len(s)
        block_level = 0
        while i < n:
            # block comment start
            if i + 1 < n and s[i] == "/" and s[i + 1] == "-":
                block_level += 1
                i += 2
                continue
            # block comment end
            if i + 1 < n and s[i] == "-" and s[i + 1] == "/" and block_level > 0:
                block_level -= 1
                i += 2
                continue
            # inside block comment: skip until closed
            if block_level > 0:
                i += 1
                continue
            # line comment: from "--" to end of line
            if i + 1 < n and s[i] == "-" and s[i + 1] == "-":
                # skip until newline (but keep the newline)
                i += 2
                while i < n and s[i] != "\n":
                    i += 1
                continue
            # otherwise copy character
            out_chars.append(s[i])
            i += 1
        # remove_comments end
        return "".join(out_chars)

    # コメント除去
    cleaned = remove_comments(text)
    lines = cleaned.splitlines(keepends=True)  # 改行を保持して分割
    # 定義抽出
    start_pat = re.compile(
        r"^(def|lemma|theorem|example|instance|axiom|variable|constant)\s"
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
            # identifier: 次のトークン（コロンや括弧が来る前まで）
            id_m = re.match(
                r"^(?:def|lemma|theorem|example|instance|axiom|variable|constant)\s+([^\s:(]+)",
                stripped_line,
            )
            ident = id_m.group(1) if id_m else "(unknown)"
            # collect until next top-level keyword or EOF
            j = i
            block_lines = []
            while j < nlines:
                cur = lines[j]
                cur_stripped = cur.lstrip()
                # stop if a new top-level definition starts (but not at the first line)
                if j != i and start_pat.match(cur_stripped):
                    break
                block_lines.append(cur)
                j += 1

            # For lemma/theorem, if there is a line containing ":= by" then truncate after that line
            truncated = False
            if keyword in ("lemma", "theorem"):
                for k, bl in enumerate(block_lines):
                    if re.search(r":=\s*by", bl):
                        # keep up to and including this line
                        block_lines = block_lines[: k + 1]
                        truncated = True
                        break

            definitions.append(
                {
                    "keyword": keyword,
                    "ident": ident,
                    "lines": block_lines,
                    "truncated": truncated,
                }
            )

            i = j
        else:
            i += 1

    # Write Markdown with requested structure
    with open(output_file, "w", encoding="utf-8") as f:
        # 先頭に改行を入れて既存テストの期待に合わせる
        f.write("\n")
        f.write("# Theorems\n\n")
        f.write(f"## {os.path.basename(input_file)}\n\n")
        for idx, item in enumerate(definitions):
            f.write(f"### {item['ident']}\n\n")
            f.write("```lean\n")
            f.write("".join(item["lines"]).rstrip() + "\n")
            if item["truncated"]:
                # indicate omission
                f.write("  ...\n")
            # 最後の要素のみ余分な空行を付けない
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
    args = parser.parse_args()
    # 入力ファイルの存在確認
    if not os.path.isfile(args.input):
        # 存在しない: エラーメッセージを表示して終了
        print(f"Error: Input file {args.input} does not exist.")
        sys.exit(1)
    # 定義抽出の実行
    extract_definitions(args.input, args.output)


if __name__ == "__main__":
    main()
