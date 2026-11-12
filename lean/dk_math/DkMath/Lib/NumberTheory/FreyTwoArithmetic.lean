/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalReduction

#print "file: DkMath.Lib.NumberTheory.FreyTwoArithmetic"

/-!
# NOTE-007: 正規化整モデルの2での c₄ 単元性

4∣B−A−1 から B−A は奇数なので、A,B は異なる偶奇を持つ。
従って A²+AB+B² は奇数である。四つの剰余組を kernel で検査し、
Frey の整数モデルの c₄ 非可除性へ戻す。冪和・原始性・指数には依存しない。
-/

namespace DkMath.Lib.NumberTheory.FreyGapCubic

/-- 整数モデルの分母条件だけで c₄ は奇数になる。FLT の方程式は不要。 -/
theorem not_two_dvd_integral_c4 (A B : ℤ) (hn : IntegralNormalization A B) :
    ¬ (2 : ℤ) ∣ (integral A B).c₄ := by
  rw [integral_c4 A B hn]
  intro hc
  have h2 : (2 : ℤ) ∣ B - A - 1 := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) hn.four
  have hf : (B : ZMod 2) - (A : ZMod 2) - 1 = 0 := by
    simpa only [Int.cast_sub, Int.cast_one] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  have hz : (A : ZMod 2) ^ 2 + (A : ZMod 2) * B + (B : ZMod 2) ^ 2 = 0 := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  generalize hA : (A : ZMod 2) = a at hf hz
  generalize hB : (B : ZMod 2) = b at hf hz
  fin_cases a <;> fin_cases b <;> revert hf hz <;> decide

end DkMath.Lib.NumberTheory.FreyGapCubic

