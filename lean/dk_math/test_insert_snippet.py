#!/usr/bin/env python3
from pathlib import Path
import tempfile
import subprocess


def test_insert_snippet_basic():
    base = Path(__file__).parent
    script = base / "theorem_picker.py"
    assert script.exists()

    # create temporary repo layout
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src = td_path / "src.lean"
        tgt = td_path / "target.lean"
        # source contains a simple def
        src.write_text("def foo : Nat := 1\n", encoding="utf-8")
        # target with header
        tgt.write_text('/- header -\n\nprint "hello"\n', encoding="utf-8")

        # run script to find and insert
        res = subprocess.run(
            [
                "python",
                str(script),
                str(src),
                str(td_path / "out.md"),
                "--find-name",
                "foo",
                "--insert-ident",
                "foo",
                "--insert-target",
                str(tgt),
                "--insert-line",
                "2",
            ],
            cwd=td_path,
            capture_output=True,
            text=True,
        )
        assert res.returncode == 0, f"script failed: {res.stderr}"
        # inserted file should exist
        inserted = tgt.with_suffix(tgt.suffix + ".inserted")
        assert inserted.exists(), "Inserted file not created"
        content = inserted.read_text(encoding="utf-8")
        assert "def foo : Nat := 1" in content


if __name__ == "__main__":
    test_insert_snippet_basic()
    print("ok")
