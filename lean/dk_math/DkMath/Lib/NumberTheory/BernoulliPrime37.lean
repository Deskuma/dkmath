/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

#print "file: DkMath.Lib.NumberTheory.BernoulliPrime37"

/-!
# 37と Bernoulli 数の検算可能な証明書

再帰式から有理数を順番に計算し、既証明の前の値だけを書き換える。
32次の再帰を素朴に繰り返し展開せず、各段の証明を共有する。
生成した数値は定理の入力候補に過ぎず、等式は Lean の kernel が検査する。
計算機外部の評価結果を公理として採用しない。

BernoulliIrregularPair は有限な分子可除性の定義である。
これと円分類群の非自明 torsion を結ぶ Kummer の判定定理は、このモジュールには含めない。
-/

namespace DkMath.Lib.NumberTheory.BernoulliPrime37

@[local simp] private theorem value_0 : bernoulli' 0 = 1 := by
  exact bernoulli'_zero

@[local simp] private theorem value_1 : bernoulli' 1 = (1 : ℚ) / 2 := by
  exact bernoulli'_one

@[local simp] private theorem value_2 : bernoulli' 2 = (1 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_3 : bernoulli' 3 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_4 : bernoulli' 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_5 : bernoulli' 5 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_6 : bernoulli' 6 = (1 : ℚ) / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_7 : bernoulli' 7 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_8 : bernoulli' 8 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_9 : bernoulli' 9 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_10 : bernoulli' 10 = (5 : ℚ) / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_11 : bernoulli' 11 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_12 : bernoulli' 12 = (-691 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_13 : bernoulli' 13 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_14 : bernoulli' 14 = (7 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_15 : bernoulli' 15 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_16 : bernoulli' 16 = (-3617 : ℚ) / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_17 : bernoulli' 17 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_18 : bernoulli' 18 = (43867 : ℚ) / 798 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_19 : bernoulli' 19 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_20 : bernoulli' 20 = (-174611 : ℚ) / 330 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_21 : bernoulli' 21 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_22 : bernoulli' 22 = (854513 : ℚ) / 138 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_23 : bernoulli' 23 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_24 : bernoulli' 24 = (-236364091 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_25 : bernoulli' 25 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_26 : bernoulli' 26 = (8553103 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_27 : bernoulli' 27 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_28 : bernoulli' 28 = (-23749461029 : ℚ) / 870 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_29 : bernoulli' 29 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_30 : bernoulli' 30 = (8615841276005 : ℚ) / 14322 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_31 : bernoulli' 31 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_32 : bernoulli' 32 = (-7709321041217 : ℚ) / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

@[local simp] private theorem value_33 : bernoulli' 33 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[local simp] private theorem value_34 : bernoulli' 34 = (2577687858367 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

/-- Mathlib の Bernoulli 数 B32 の厳密値。符号規約も bernoulli の定義と一致する。 -/
theorem bernoulli_thirtyTwo : bernoulli 32 = (-7709321041217 : ℚ) / 510 := by
  norm_num [bernoulli]

/-- B32 の既約分子に37が現れ、分母には現れない。 -/
theorem thirtySeven_dvd_numerator : (37 : ℤ) ∣ (bernoulli 32).num := by
  rw [bernoulli_thirtyTwo]
  norm_num

theorem thirtySeven_not_dvd_denominator : ¬ 37 ∣ (bernoulli 32).den := by
  rw [bernoulli_thirtyTwo]
  norm_num

/-- 古典的な Bernoulli 非正則対の有限算術条件。類群との同値は仮定しない。 -/
def BernoulliIrregularPair (p n : ℕ) : Prop :=
  p.Prime ∧ 2 ≤ n ∧ Even n ∧ n ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli n).num

/-- p=37 では、調べる範囲の非正則対は32だけである。 -/
theorem irregular_pair_thirtySeven_iff (n : ℕ) : BernoulliIrregularPair 37 n ↔ n = 32 := by
  constructor
  · intro h
    have hn : n ≤ 34 := h.2.2.2.1
    interval_cases n <;> (first | rfl | norm_num [BernoulliIrregularPair, bernoulli] at h)
  · rintro rfl
    norm_num [BernoulliIrregularPair, bernoulli]

/-- 比較指数11では Bernoulli 非正則対がない。類数1の既存証明とは独立な有限検査。 -/
theorem no_irregular_pair_eleven : ¬ ∃ n, BernoulliIrregularPair 11 n := by
  rintro ⟨n, h⟩
  have hn : n ≤ 8 := h.2.2.2.1
  interval_cases n <;> norm_num [BernoulliIrregularPair, bernoulli] at h

/-- 比較指数13も同じ有限検査で非正則対を持たない。 -/
theorem no_irregular_pair_thirteen : ¬ ∃ n, BernoulliIrregularPair 13 n := by
  rintro ⟨n, h⟩
  have hn : n ≤ 10 := h.2.2.2.1
  interval_cases n <;> norm_num [BernoulliIrregularPair, bernoulli] at h

end DkMath.Lib.NumberTheory.BernoulliPrime37
