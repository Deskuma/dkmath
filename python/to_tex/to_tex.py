#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# KaTeX to LaTeX converter (simple)

import re
import argparse


def to_tex(katex: str) -> str:
    # Simple replacements
    replacements = {
        r"\\cdot": r"\cdot",
        r"\\frac{([^}]*)}{([^}]*)}": r"\frac{\1}{\2}",
        r"\\left\(": r"\left(",
        r"\\right\)": r"\right)",
        r"\\left\[": r"\left[",
        r"\\right\]": r"\right]",
        r"\\sqrt{([^}]*)}": r"\sqrt{\1}",
        r"\\sum_{([^}]*)}^{([^}]*)}": r"\sum_{\1}^{\2}",
        r"\\int_{([^}]*)}^{([^}]*)}": r"\int_{\1}^{\2}",
        r"\\infty": r"\infty",
        r"\\pi": r"\pi",
        r"\\theta": r"\theta",
        r"\\cdots": r"\cdots",
        # Convert KaTeX delimiters to dollar delimiters:
        # \( ... \) -> $...$  (inline math)
        # \[ ... \] -> $$...$$ (display math)
    }

    tex = katex
    for pattern, replacement in replacements.items():
        # Use a callable replacement to avoid re.sub template parsing of backslashes
        def _repl(match, rep=replacement):
            s = rep
            # substitute numeric backreferences \1, \2, ... with match groups
            for i, g in enumerate(match.groups(), start=1):
                s = s.replace(f"\\{i}", g or "")
            return s

        tex = re.sub(pattern, _repl, tex)

    # Convert KaTeX delimiters to dollar delimiters robustly:
    # \( ... \) -> $...$  (inline math)
    # \[ ... \] -> $$...$$ (display math)
    tex = re.sub(
        re.escape(r"\(") + r"([\s\S]*?)" + re.escape(r"\)"),
        lambda m: f"${m.group(1)}$",
        tex,
    )
    tex = re.sub(
        re.escape(r"\[") + r"([\s\S]*?)" + re.escape(r"\]"),
        lambda m: f"$${m.group(1)}$$",
        tex,
    )

    return tex


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert KaTeX to LaTeX")
    parser.add_argument("input", help="KaTeX expression to convert")
    parser.add_argument(
        "-f", "--file", action="store_true", help="Indicates that input is a file"
    )
    parser.add_argument("-o", "--output", default=None, help="Output file (optional)")
    args = parser.parse_args()

    if args.output:
        with open(args.output, "w") as f:
            if args.file:
                with open(args.input, "r") as infile:
                    katex_content = infile.read()
                f.write(to_tex(katex_content))
            else:
                f.write(to_tex(args.input))
    else:
        if args.file:
            with open(args.input, "r") as infile:
                katex_content = infile.read()
            print(to_tex(katex_content))
        else:
            print(to_tex(args.input))
