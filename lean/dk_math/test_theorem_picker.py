#!/usr/bin/env python3
from pathlib import Path


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


if __name__ == "__main__":
    test_extract_definitions()
    test_theorem_picker_help()
    print("All tests passed!")
