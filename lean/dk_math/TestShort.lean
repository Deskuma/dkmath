/-
Sample Lean file for testing theorem_picker.py --short option.

このファイルは test_theorem_picker.py で使用されるテストサンプルです。
--short オプションの動作確認のため、複数行の `by` 証明を含んでいます。
-/

theorem simple_theorem : True := by
  trivial

theorem multi_line_proof : 1 + 1 = 2 := by
  rfl
  -- 複数行の証明

lemma example_lemma (n : Nat) : n = n := by
  rfl
  -- 自明な補題

def simple_def : Nat := 42

-- `by` を含まない定義
def another_def (x : Nat) : Nat := x + 1

-- 複数行の `by` 証明
theorem complex_proof (a b : Nat) : a + b = b + a := by
  apply Nat.add_comm
  -- コミュータティブ性の証明
