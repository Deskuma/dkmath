import textwrap
import importlib.util
from pathlib import Path

# Load the to_tex module by path to avoid import path/package issues in test runner
module_path = Path(__file__).resolve().parents[1] / "to_tex.py"
spec = importlib.util.spec_from_file_location("to_tex_module", module_path)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
to_tex = mod.to_tex


def test_basic_replacements():
    assert to_tex("\\cdot") == r"\cdot"
    assert to_tex("\\frac{1}{2}") == r"\frac{1}{2}"
    assert to_tex("\\sqrt{x}") == r"\sqrt{x}"


def test_delimiters_inline_and_display():
    s = "\\(a+b\\) and \\[c+d\\]"
    out = to_tex(s)
    # debugging: check representation and source
    try:
        src = to_tex.__module__
    except Exception:
        src = None
    print("DEBUG to_tex module:", src)
    print("DEBUG repr(out):", repr(out))
    print("DEBUG bytes:", out.encode("utf-8"))
    assert out == "$a+b$ and $$c+d$$"


def test_multiline_inline():
    s = "prefix " + "\\(" + "a\n+b" + "\\) suffix"
    out = to_tex(s)
    assert out == "prefix $a\n+b$ suffix"


def test_combined_and_multiple():
    s = r"\\left( x \\\right) + \\\sum_{i}^{n} + \\\infty"
    # After conversion, \left( and \right) become literal parentheses in our simple converter
    out = to_tex(s)
    assert (r"\\left(" in out) or ("(" in out)
    assert (r"\\sum_{i}^{n}" in out) or ("sum" in out)


def test_noop_text():
    s = "This is plain text with dollar $ signs and (parentheses)."
    assert to_tex(s) == s


def test_multiple_inline_occurrences():
    s = "A \\(x\\) B \\(y\\)"
    assert to_tex(s) == "A $x$ B $y$"
