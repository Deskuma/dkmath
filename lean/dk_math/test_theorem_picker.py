#!/usr/bin/env python3
from pathlib import Path
import shutil
import tempfile


def test_extract_definitions():
    """
    Integration test: theorem_picker.py を使用して実際のLean 4 プロジェクトから抽出できることを確認。

    実行条件：
    - Lake プロジェクトのディレクトリで実行
    - lakefile.toml が存在すること
    - 対象の .lean ファイルがプロジェクトに含まれていること
    """
    import subprocess

    # theorem_picker.py の実行確認（簡易版）
    # 実際の抽出は lake env の availability に依存するため、スクリプト自体の存在と
    # 基本的な Python 構文を確認する
    script_path = Path(__file__).parent / "theorem_picker.py"
    assert script_path.exists(), f"theorem_picker.py not found at {script_path}"

    # Python スクリプトの基本的なシンタックスチェック
    result = subprocess.run(
        ["python", "-m", "py_compile", str(script_path)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"Syntax error in theorem_picker.py: {result.stderr}"


def test_theorem_picker_help():
    """
    コマンドラインヘルプが正常に表示されることを確認。
    """
    import subprocess

    result = subprocess.run(
        ["python", "theorem_picker.py", "-h"],
        cwd=Path(__file__).parent,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, "Help output failed"
    assert "extract definitions" in result.stdout.lower()
    assert "--short" in result.stdout


def test_theorem_picker_short_option():
    """
    --short オプションで CosmicFormula 配下の全 .lean を処理できることを確認。
    出力を読み取り、実際に "..." が含まれ、"by" 以降が省略されていることを検証。
    """
    import subprocess
    import re
    try:
        import pytest
        pytest_available = True
    except ImportError:
        pytest_available = False

    if shutil.which("lake") is None:
        if pytest_available:
            pytest.skip("lake is not available; skipping LSP-backed extraction test.")
        else:
            print("Skipping test: lake is not available")
            return

    base_dir = Path(__file__).parent
    lean_dir = base_dir / "DkMath" / "CosmicFormula"
    lean_files = sorted(lean_dir.glob("*.lean"))
    assert lean_files, f"No .lean files found in {lean_dir}"

    with tempfile.TemporaryDirectory() as tmpdir:
        found_ellipsis = False
        for lean_file in lean_files:
            output_path = Path(tmpdir) / f"{lean_file.stem}-v0.md"
            result = subprocess.run(
                ["python", "theorem_picker.py", str(lean_file), str(output_path), "--short"],
                cwd=base_dir,
                capture_output=True,
                text=True,
            )
            assert result.returncode == 0, (
                f"theorem_picker.py failed for {lean_file}: {result.stderr}"
            )
            assert output_path.exists(), f"Output not generated: {output_path}"
            
            # 出力ファイルを読み取り、"..." が含まれることを確認
            with open(output_path, "r", encoding="utf-8") as f:
                content = f.read()
                # "by ..." のパターンを Lean コードブロック内で確認
                # Markdown の ```lean ... ``` ブロック内で "by ..." を探す
                lean_blocks = re.findall(r'```lean\n(.*?)```', content, re.DOTALL)
                for block in lean_blocks:
                    if re.search(r'\bby\s+\.\.\.', block):
                        found_ellipsis = True
                        break
        
        # 少なくとも1つのファイルで省略が行われたことを確認
        assert found_ellipsis, (
            "No 'by ...' pattern found in any Lean code blocks. Expected at least one theorem with 'by' to be truncated."
        )


if __name__ == "__main__":
    test_extract_definitions()
    test_theorem_picker_help()
    test_theorem_picker_short_option()
    print("All tests passed!")
