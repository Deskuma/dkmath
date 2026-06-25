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

# この単語を含む括弧は、数式の説明語として扱います。
# 例: (prime) や (log) は本文中では数式寄りの語として \(...\) に直します。
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

# 1文字の変数や、よく使う識別子を数式として扱うための一覧です。
# 例: (p), (q), (n), (pOf) を \(p\), \(q\), \(n\), \(pOf\) にします。
# ここに名前を追加すると、その名前だけの括弧も変換対象になります。
MATH_ATOMS = {
    "A",
    "B",
    "C",
    "D",
    "E",
    "F",
    "G",
    "H",
    "I",
    "J",
    "K",
    "L",
    "M",
    "N",
    "O",
    "P",
    "Q",
    "R",
    "S",
    "T",
    "U",
    "V",
    "W",
    "X",
    "Y",
    "Z",
    "a",
    "b",
    "c",
    "d",
    "e",
    "f",
    "g",
    "h",
    "i",
    "j",
    "k",
    "l",
    "m",
    "n",
    "o",
    "p",
    "q",
    "r",
    "s",
    "t",
    "u",
    "v",
    "w",
    "x",
    "y",
    "z",
    "pOf",
    "q2",
}


def read_md(filename: Path, encoding: str = "utf-8") -> str:
    # Markdown ファイル全体を文字列として読み込みます。
    return filename.read_text(encoding=encoding)


def write_md(filename: Path, content: str, encoding: str = "utf-8") -> None:
    # 変換後の Markdown をファイルに書き戻します。
    filename.write_text(content, encoding=encoding)


def is_escaped(text: str, index: int) -> bool:
    # text[index] の直前にあるバックスラッシュの数を数えます。
    # 奇数個なら、その文字はエスケープされています。
    # 例: \( の "(" はエスケープ済みなので、通常の "(" として扱いません。
    backslashes = 0
    i = index - 1
    while i >= 0 and text[i] == "\\":
        backslashes += 1
        i -= 1
    return backslashes % 2 == 1


def closing_backtick(text: str, start: int) -> int:
    # inline code の終端を探します。
    # `code` だけでなく ``code ` inside`` のような複数バッククォートにも対応します。
    match = re.match(r"`+", text[start:])
    if match is None:
        return -1
    ticks = match.group(0)
    return text.find(ticks, start + len(ticks))


def closing_inline_dollar(text: str, start: int) -> int:
    # $...$ の終端を探します。
    # すでに inline math になっている範囲は、このスクリプトでは触りません。
    i = start + 1
    while i < len(text):
        if text[i] == "$" and not is_escaped(text, i):
            return i
        i += 1
    return -1


def matching_paren(text: str, start: int) -> int:
    # start にある "(" と対応する ")" の位置を探します。
    # 正規表現では難しい ((x+u)^d) のような入れ子括弧を depth で数えます。
    depth = 0
    i = start
    while i < len(text):
        ch = text[i]
        if ch == "`":
            # inline code の中にある括弧は無視します。
            end = closing_backtick(text, i)
            if end == -1:
                return -1
            i = end + 1
            continue
        if ch == "\\" and i + 1 < len(text):
            # \(...\) など、バックスラッシュ付きの文字は既存の記法として飛ばします。
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
    # 括弧の中身が「数式らしい」かを判定します。
    # True なら (expr) を \(expr\) に変換します。
    # False なら普通の日本語・英語の括弧として残します。
    stripped = expr.strip()
    if not stripped:
        return False
    if "\n" in stripped:
        # inline KaTeX なので、複数行にまたがる括弧は変換しません。
        return False
    if any(ch in MATH_CHARS for ch in stripped):
        # ^, _, =, +, \ などがあれば数式とみなします。
        return True
    if re.fullmatch(r"\d+(?:\.\d+)?", stripped):
        # (1), (10), (1.5) のような数字だけの括弧も数式とみなします。
        return True
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", stripped):
        # (p) や (pOf) のような識別子は、MATH_ATOMS に登録済みなら数式です。
        return stripped in MATH_ATOMS
    if ("(" in stripped or ")" in stripped) and re.search(r"[A-Za-z0-9]", stripped):
        # ((x+u)^d) の外側を外した中身には、まだ括弧が残ります。
        # そのような入れ子構造は数式として扱います。
        return True
    if re.search(r"\b(?:[A-Za-z]\d|\d[A-Za-z])\b", stripped):
        # x1 や 2x のような英数字の結合は数式寄りとみなします。
        return True
    if re.fullmatch(r"[A-Za-z](?:\s*,\s*[A-Za-z0-9_]+)+", stripped):
        # (x, y) のような変数リストを数式として扱います。
        return True
    words = set(re.findall(r"[A-Za-z][A-Za-z0-9_-]*", stripped))
    # Big / prime / log など、MATH_WORDS に含まれる語があれば数式として扱います。
    return bool(words & MATH_WORDS)


def transform_text_segment(text: str) -> str:
    # コードブロックや $$ ブロックではない、通常の本文1行を変換します。
    # 左から右へ1文字ずつ見て、変換できる箇所だけ out に置き換えて入れます。
    out: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "`":
            # inline code は Markdown のコード片なので、中身をそのまま残します。
            end = closing_backtick(text, i)
            if end == -1:
                out.append(text[i:])
                break
            out.append(text[i : end + len(re.match(r"`+", text[i:]).group(0))])
            i = end + len(re.match(r"`+", text[i:]).group(0))
            continue
        if ch == "$" and not is_escaped(text, i):
            # すでに $...$ になっている inline math は、そのまま残します。
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
            # すでに \(...\) になっている inline KaTeX は二重変換しません。
            end = text.find(r"\)", i + 2)
            if end != -1:
                out.append(text[i : end + 2])
                i = end + 2
                continue
        if ch == "(" and not is_escaped(text, i):
            # 普通の "(" を見つけたら、対応する ")" までを解析します。
            end = matching_paren(text, i)
            if end != -1:
                expr = text[i + 1 : end]
                if looks_like_math(expr):
                    # 数式らしい括弧だけを \( ... \) に変換します。
                    out.append(r"\(")
                    out.append(expr.strip())
                    out.append(r"\)")
                    i = end + 1
                    continue
        out.append(ch)
        i += 1
    return "".join(out)


def transform_markdown(content: str) -> str:
    # Markdown 全体を変換します。
    # ``` ... ``` と $$ ... $$ の範囲は保護し、それ以外の行だけ transform_text_segment に渡します。
    lines = content.splitlines(keepends=True)
    out: list[str] = []
    in_fence = False
    in_math_block = False

    for line in lines:
        stripped = line.lstrip()
        if stripped.startswith("```"):
            # fenced code block の開始/終了を切り替えます。
            out.append(line)
            in_fence = not in_fence
            continue

        if not in_fence and stripped.strip() == "$$":
            # display math block の開始/終了を切り替えます。
            out.append(line)
            in_math_block = not in_math_block
            continue

        if in_fence or in_math_block:
            # コードブロック・数式ブロックの中は絶対に変更しません。
            out.append(line)
        else:
            # 通常本文だけ inline KaTeX の修正対象にします。
            out.append(transform_text_segment(line))

    return "".join(out)


def unified_diff(before: str, after: str, filename: Path) -> str:
    # --check 用に、変換前後の差分を unified diff 形式で作ります。
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile=f"{filename} (before)",
            tofile=f"{filename} (after)",
        )
    )


def parse_args() -> argparse.Namespace:
    # コマンドライン引数を定義します。
    # --check は確認だけ、-i は上書き、-o は別ファイルへの出力です。
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
    # ここがコマンドとして実行されたときの入口です。
    args = parse_args()
    before = read_md(args.file, args.encoding)
    after = transform_markdown(before)

    if args.check:
        # --check ではファイルを書き換えず、必要な変更を差分として表示します。
        if before != after:
            sys.stdout.write(unified_diff(before, after, args.file))
            return 1
        return 0

    if args.in_place and args.output is not None:
        # 同時に「上書き」と「別ファイル出力」を指定すると曖昧なのでエラーにします。
        print("--in-place and --output cannot be used together", file=sys.stderr)
        return 2

    if args.in_place:
        # -i / --in-place の場合だけ、入力ファイルを上書きします。
        if before != after:
            write_md(args.file, after, args.encoding)
        return 0

    if args.output is not None:
        # -o / --output の場合は、指定された別ファイルに書き出します。
        write_md(args.output, after, args.encoding)
        return 0

    # 何も指定しない場合は、変換結果を標準出力に表示します。
    sys.stdout.write(after)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
