/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.HomogeneousPowerQuotient

#print "file: DkMathTest.NumberTheory.HomogeneousPowerQuotient"

namespace DkMathTest.NumberTheory.HomogeneousPowerQuotient

open DkMath.Lib.NumberTheory

/-! The generic congruence is instantiated at the three exponents used by the
FLT7 development. These are only finite calibration examples. -/

example (x y : ℤ) :
    x - y ∣ homogeneousPowerQuotient x y 3 - (3 : ℤ) * y ^ (3 - 1) := by
  exact gap_dvd_homogeneous_sub_natCast_mul x y 3

example (x y : ℤ) :
    x - y ∣ homogeneousPowerQuotient x y 5 - (5 : ℤ) * y ^ (5 - 1) := by
  exact gap_dvd_homogeneous_sub_natCast_mul x y 5

example (x y : ℤ) :
    x - y ∣ homogeneousPowerQuotient x y 7 - (7 : ℤ) * y ^ (7 - 1) := by
  exact gap_dvd_homogeneous_sub_natCast_mul x y 7

/-! An integer common-prime instance: for `x = 8`, `y = 1`, and `n = 7`,
the prime `7` divides both the gap and the quotient, hence the theorem
localizes that support to the exponent. -/

example : (7 : ℤ) ∣ (7 : ℤ) := by
  apply prime_dvd_exponent_cast_of_coprime_gap_and_homogeneous
    (7 : ℤ) 8 1 7 (by norm_num) (by norm_num)
  · norm_num
  · have hcong := gap_dvd_homogeneous_sub_natCast_mul (8 : ℤ) 1 7
    have hseven : (7 : ℤ) ∣ (7 : ℤ) * (1 : ℤ) ^ (7 - 1) := by norm_num
    have hadd := dvd_add hcong hseven
    norm_num at hadd ⊢
    exact hadd

end DkMathTest.NumberTheory.HomogeneousPowerQuotient
