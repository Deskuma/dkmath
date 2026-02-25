#!/usr/bin/env python3
from pathlib import Path
import tempfile
import subprocess


def test_find_definition_s0():
    """Static search should find `S0_nat` definition in the repo."""
    script = Path(__file__).parent / "theorem_picker.py"
    assert script.exists(), "theorem_picker.py not found"

    base = Path(__file__).parent
    lean_root = base
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "found.md"
        # call the script with --find-name S0_nat
        res = subprocess.run(
            [
                "python",
                str(script),
                str(base / "TestShort.lean"),
                str(out),
                "--find-name",
                "S0_nat",
            ],
            cwd=base,
            capture_output=True,
            text=True,
        )
        # script should exit cleanly
        assert res.returncode == 0, f"script failed: {res.stderr}"
        assert out.exists(), "output file not generated"
        txt = out.read_text(encoding="utf-8")
        assert "S0_nat" in txt, "S0_nat not found in output"


if __name__ == "__main__":
    test_find_definition_s0()
    print("ok")
