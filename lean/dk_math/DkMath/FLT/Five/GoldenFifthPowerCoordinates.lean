/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenFifthPower

#print "file: DkMath.FLT.Five.GoldenFifthPowerCoordinates"

namespace DkMath.FLT.Five

/-- First-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5

/-- Second-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthSndPoly (p q : ℤ) : ℤ :=
  5 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 +
    3 * p * q ^ 3 + q ^ 4)

theorem goldenPow_five_fst (gamma : GoldenInt) :
    (goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring

theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring

theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide

/-- Second coordinate after the representative unit `1`. -/
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_zero]
  simp only [goldenMul]
  rw [goldenPow_five_snd]
  ring

/-- Second coordinate after the representative unit `phi`. -/
theorem golden_unit_one_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 1) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_one]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring

/-- Second coordinate after the representative unit `phi^2`. -/
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_two]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring

/-- Second coordinate after the representative unit `phi^3`. -/
theorem golden_unit_three_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 3) (goldenPow gamma 5)).snd =
      2 * goldenFifthFstPoly gamma.fst gamma.snd +
        3 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_three]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring

/-- Second coordinate after the representative unit `phi^4`. -/
theorem golden_unit_four_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 4) (goldenPow gamma 5)).snd =
      3 * goldenFifthFstPoly gamma.fst gamma.snd +
        5 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_four]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring

/-- Negating a unit representative negates the resulting second coordinate. -/
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
  rw [neg_mul]
  rfl

end DkMath.FLT.Five
