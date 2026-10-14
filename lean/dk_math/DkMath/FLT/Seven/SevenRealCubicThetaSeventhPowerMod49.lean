/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower

#print "file: DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerMod49"

namespace DkMath.FLT.Seven.SevenRealCubicInt

private theorem dvd_seven_of_zmod_seven_zero (m : ℤ)
    (hm : (m : ZMod 7) = 0) : (7 : ℤ) ∣ m := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m 7).mp hm

theorem thetaLinear_pow_seven_mod49_neutral (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaLinearInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * B * A ^ 6 := by
  have hB : (7 : ℤ) ∣ seventhThetaLinearBFactor A B C - A ^ 6 := by
    apply dvd_seven_of_zmod_seven_zero
    push_cast
    rw [seventhThetaLinearBFactor_modSeven]
    ring
  rcases hB with ⟨qB, hqB⟩
  refine ⟨B * qB + C ^ 2 * seventhThetaLinearCFactor A C, ?_⟩
  rw [thetaLinear_pow_seven]
  simp only [seventhThetaLinearQuotient]
  linear_combination 7 * B * hqB

theorem thetaSquare_pow_seven_mod49_neutral (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaSquareInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * (C * A ^ 6 + 3 * B ^ 2 * A ^ 5) := by
  have hC : (7 : ℤ) ∣ seventhThetaSquareCFactor A B C - A ^ 6 := by
    apply dvd_seven_of_zmod_seven_zero
    push_cast
    rw [seventhThetaSquareCFactor_modSeven]
    ring
  have hB : (7 : ℤ) ∣ seventhThetaSquareBFactor A B - 3 * A ^ 5 := by
    apply dvd_seven_of_zmod_seven_zero
    push_cast
    rw [seventhThetaSquareBFactor_modSeven]
    ring
  rcases hC with ⟨qC, hqC⟩
  rcases hB with ⟨qB, hqB⟩
  refine ⟨C * qC + B ^ 2 * qB, ?_⟩
  rw [thetaSquare_pow_seven]
  simp only [seventhThetaSquareQuotient]
  linear_combination 7 * C * hqC + 7 * B ^ 2 * hqB

end DkMath.FLT.Seven.SevenRealCubicInt
