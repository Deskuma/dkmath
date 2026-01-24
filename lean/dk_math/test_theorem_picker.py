#!/usr/bin/env python3
import os
import re
import argparse
from theorem_picker import extract_definitions


def test_extract_definitions():
    # テスト用の入力と出力
    input_file = "test_input.lean"
    output_file = "test_output.md"

    # テスト用の Lean コードを含むファイルを作成
    with open(input_file, "w", encoding="utf-8") as f:
        f.write(
            """
def test1 : Nat := 1
lemma test2 : Nat := by
  exact 2
theorem test3 : Nat := by
  exact 3
"""
        )

    # 定義を抽出
    extract_definitions(input_file, output_file)

    # 出力ファイルの内容を確認
    with open(output_file, "r", encoding="utf-8") as f:
        output = f.read()

    # 期待される出力
    expected_output = """
# Theorems

## test_input.lean

### test1

```lean
def test1 : Nat := 1
```

### test2

```lean
lemma test2 : Nat := by
  ...
```

### test3

```lean
theorem test3 : Nat := by
  ...
```
"""

    assert output == expected_output, f"Expected:\n{expected_output}\nGot:\n{output}"

    # テスト用のファイルをクリーンアップ
    os.remove(input_file)
    os.remove(output_file)
