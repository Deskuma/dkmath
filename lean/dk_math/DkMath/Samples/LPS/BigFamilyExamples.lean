import Mathlib
import DkMath.Samples.LPS.BigFamily
import DkMath.Samples.LPS.BigFamilyInt
import DkMath.Samples.LPS.PowerSwap
import DkMath.Samples.LPS.GapFillRank

namespace DkMath
namespace Samples
namespace BigFamilyExamples

/-! ## 反転指数交点 `16` の標本 -/

/-- `2^4 = 4^2` は PowerSwap の基本標本。 -/
theorem powerSwap_2_4 : PowerSwap 2 4 :=
  powerSwap_two_four

/-- 同じ `16` は 2 乗 1 項 (`4^2`) で埋まる。 -/
theorem fillable_pow2_16_exact_one : FillableByPowSumExact 2 16 1 :=
  fillable_sq_16_exact_one

/-- 同じ `16` は 4 乗 1 項 (`2^4`) でも埋まる。 -/
theorem fillable_pow4_16_exact_one : FillableByPowSumExact 4 16 1 := by
  refine ⟨fun _ => 2, ?_⟩
  simp

/-- Big-family (`ℕ`) 側での `16` 観測。 -/
example : BigFamily.big 2 3 1 = 16 := by
  norm_num [BigFamily.big]

/-- Big-family (`ℤ`) 側での `16` 観測。 -/
example : BigFamilyInt.big 2 3 1 = 16 := by
  norm_num [BigFamilyInt.big]

/-! ## 三乗補正 `216` の標本 -/

/-- `216 = 6^3` は 1 項の 3 乗和。 -/
theorem fillable_cube_216_exact_one_sample : FillableByPowSumExact 3 216 1 :=
  fillable_cube_216_exact_one

/-- `216 = 3^3 + 4^3 + 5^3` は 3 項の 3 乗和。 -/
theorem fillable_cube_216_exact_three_sample : FillableByPowSumExact 3 216 3 :=
  fillable_cube_216_exact_three

/-- 同じ値 `216` が異なる filling を持つことの数式確認。 -/
example : (6 : ℕ) ^ 3 = 3 ^ 3 + 4 ^ 3 + 5 ^ 3 := by
  norm_num

/-! ## residual 観測（差分の同次数和） -/

/-- 差分 `6^3 - 5^3` は `3^3 + 4^3` に一致する。 -/
theorem residual_cube_6_5_eq_two_cubes_nat :
    (6 : ℕ) ^ 3 - 5 ^ 3 = 3 ^ 3 + 4 ^ 3 := by
  norm_num

/-- 上の差分は 3 乗 2 項で埋まる。 -/
theorem residual_cube_6_5_fillable_exact_two :
    FillableByPowSumExact 3 ((6 : ℕ) ^ 3 - 5 ^ 3) 2 := by
  refine ⟨![3, 4], ?_⟩
  norm_num

/-- `ℤ`-Big-family 観測での差分形。 -/
theorem residual_big_minus_core_eq_two_cubes_int :
    BigFamilyInt.big 3 5 1 - BigFamilyInt.core 3 5 1 =
      (3 : ℤ) ^ 3 + 4 ^ 3 := by
  norm_num [BigFamilyInt.big, BigFamilyInt.core]

/-! ## 三平方補正項族（整数版） -/

/--
`(2m)^2 + (2n)^2 + (m^2+n^2-1)^2 = (m^2+n^2+1)^2`

三平方補正項族の基本恒等式（`ℤ` 版）。
-/
theorem three_square_correction_family (m n : ℤ) :
    (2 * m) ^ 2 + (2 * n) ^ 2 + (m ^ 2 + n ^ 2 - 1) ^ 2 =
      (m ^ 2 + n ^ 2 + 1) ^ 2 := by
  ring

end BigFamilyExamples
end Samples
end DkMath
