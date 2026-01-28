/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath.SilverRatio.Sqrt2

noncomputable section

/-- √2 as a real number -/
def sqrt2 : ℝ := Real.sqrt 2

/-- silver ratio: σ := 1 + √2 -/
def sigma : ℝ := 1 + sqrt2

/-- Key lemma: sqrt2 ^ 2 = 2 (robust) -/
@[simp] lemma sqrt2_sq : sqrt2 ^ 2 = (2 : ℝ) := by
  unfold sqrt2
  simp [pow_two, Real.mul_self_sqrt]

/-- Key lemma: sqrt2 ^ 2 = 2 (norm_num) -/
@[simp] lemma sqrt2_sq' : sqrt2 ^ 2 = 2 := by
  unfold sqrt2
  norm_num

/-- Key lemma: sqrt2 * sqrt2⁻¹ = 1 -/
@[simp] lemma sqrt2_mul_inv : sqrt2 * sqrt2⁻¹ = 1 := by
  unfold sqrt2
  norm_num [Real.sqrt_mul_self]

/-- Key lemma: sqrt2⁻¹ = sqrt2 / 2 (rationalize denominator) -/
@[simp] lemma sqrt2_inv : sqrt2⁻¹ = sqrt2 / 2 := by
  field_simp [sqrt2]
  rw [sqrt2_sq]

-- Supporting lemmas for algebraic manipulations

/-- sqrt2 > 0 -/
lemma sqrt2_pos : 0 < sqrt2 := by
  unfold sqrt2
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

/-- sqrt2 ≠ 0 -/
lemma sqrt2_ne_zero : sqrt2 ≠ 0 := ne_of_gt sqrt2_pos

/-- sqrt2 is irrational -/
lemma sqrt2_irrational : Irrational sqrt2 := by
  unfold sqrt2
  exact irrational_sqrt_two

-- Supporting lemmas for algebraic manipulations

/-- (sqrt2 - 1)² = 3 - 2·sqrt2 -/
lemma sqrt2_minus_one_sq : (sqrt2 - 1) ^ 2 = 3 - 2 * sqrt2 := by
  have h := sqrt2_sq
  calc
    (sqrt2 - 1) ^ 2
      = sqrt2 ^ 2 - 2 * sqrt2 + 1 := by ring
    _ = 2 - 2 * sqrt2 + 1 := by rw [h]
    _ = 3 - 2 * sqrt2 := by linarith

/-- 1/sqrt2 = sqrt2/2 (alternative form) -/
lemma one_div_sqrt2 : (1 : ℝ) / sqrt2 = sqrt2 / 2 := by
  field_simp [sqrt2_ne_zero]
  rw [sqrt2_sq]

/-- sqrt2/2 > 0 -/
lemma sqrt2_div_two_pos : 0 < sqrt2 / 2 := by
  exact div_pos sqrt2_pos (by norm_num : (0 : ℝ) < 2)

/-- (sqrt2/2)² = 1/2 -/
lemma sqrt2_div_two_sq : (sqrt2 / 2) ^ 2 = 1 / 2 := by
  have h := sqrt2_sq
  field_simp
  rw [h]

end -- noncomputable section

end DkMath.SilverRatio.Sqrt2
