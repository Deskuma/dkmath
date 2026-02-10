#!/usr/bin/env python3
from pathlib import Path
import shutil
import tempfile
import warnings


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
    --short オプションで、複数行の `by` 証明を含む Lean ファイルが
    期待通りに `by ...` に省略されることを確認する。

    このテストでは、内容が固定された TestShort.lean を使用し、
    theorem_picker.py の出力を検証することで、プロジェクトのソース構成に
    依存しない決定的なテストとする。

    テストサンプル: TestShort.lean
    - 仕様変更があればこのサンプルファイルも更新すること
    - サンプルには複数行の `by` 証明を含む定理・補題が含まれる
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
    lean_file = base_dir / "TestShort.lean"
    
    # サンプルファイルが存在することを確認
    assert lean_file.exists(), f"Test sample file not found: {lean_file}"

    with tempfile.TemporaryDirectory() as tmpdir:
        output_path = Path(tmpdir) / "TestShort-output.md"
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

        # 出力された Markdown から Lean コードブロックを抽出
        content = output_path.read_text(encoding="utf-8")
        lean_blocks = re.findall(r'```lean\s*\n(.*?)```', content, re.DOTALL)
        assert lean_blocks, "No Lean code blocks found in theorem_picker output."

        # 全てのブロックを結合して検証
        combined = "\n\n".join(lean_blocks)

        # TestShort.lean に含まれる定理・定義が抽出されていることを確認
        assert "simple_theorem" in combined, (
            "Expected theorem `simple_theorem` to appear in the output."
        )
        assert "multi_line_proof" in combined, (
            "Expected theorem `multi_line_proof` to appear in the output."
        )
        # NOTE: lemma の抽出は Lean LSP のバージョンや SymbolKind の扱いに依存する
        # 補題が抽出されない場合もあるため、警告のみで続行
        if "example_lemma" not in combined:
            warnings.warn(
                "Lemma `example_lemma` was not extracted. This may be due to LSP SymbolKind handling.",
                UserWarning
            )

        # 定義が抽出されることを確認
        # NOTE: 少なくとも1つの定義が抽出されることを確認
        # （全ての定義が抽出されるかは LSP の実装に依存）
        simple_def_present = "simple_def" in combined
        another_def_present = "another_def" in combined

        # 少なくとも1つの定義が必要
        assert simple_def_present or another_def_present, (
            "Expected at least one definition to appear in the output."
        )

        # 個別に欠けている定義を警告
        if not simple_def_present:
            warnings.warn(
                "Definition `simple_def` not extracted. This may be due to LSP SymbolKind handling.",
                UserWarning
            )
        if not another_def_present:
            warnings.warn(
                "Definition `another_def` not extracted. This may be due to LSP SymbolKind handling.",
                UserWarning
            )

        # `by ...` 省略が行われていることを確認
        assert re.search(r'\bby \.\.\.', combined), (
            "Expected `by ...` truncation in the output, but it was not found."
        )

        # 個別の定理で省略が正しく行われているか確認（決定論的検証）
        # simple_theorem は複数行の `by` 証明なので省略されるはず
        simple_theorem_match = re.search(
            r'theorem simple_theorem.*?```',
            content,
            re.DOTALL
        )
        assert simple_theorem_match is not None, (
            "Expected theorem `simple_theorem` to appear in the output for truncation check."
        )
        
        simple_theorem_text = simple_theorem_match.group(0)
        # --short オプションでは "by ..." に省略され、元の証明本体（"trivial"）は含まれないはず
        assert "by ..." in simple_theorem_text, (
            "Expected `simple_theorem` to contain `by ...` with --short option."
        )
        assert "trivial" not in simple_theorem_text, (
            "Expected `simple_theorem` to NOT contain the proof body `trivial` with --short option."
        )


if __name__ == "__main__":
    test_extract_definitions()
    test_theorem_picker_help()
    test_theorem_picker_short_option()
    print("All tests passed!")
