/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

#print "file: DkMath.CosmicFormula.Projection.NormalizedGrid"

/-!
# Finite normalized grid

The normalized `1 / k` grid is treated as a finite real-coordinate object.
The approximation theorem below is pointwise and finite; it does not assert a
dense limit or any arithmetic realization of grid points.
-/

namespace DkMath.CosmicFormula.Projection

noncomputable section

/-- The endpoint-inclusive normalized grid at denominator `k`. -/
def normalizedGrid (k : ℕ) : Finset ℝ :=
  (Finset.range (k + 1)).image (fun j : ℕ => (j : ℝ) / (k : ℝ))

/-- Every indexed point with `j ≤ k` belongs to the normalized grid. -/
theorem mem_normalizedGrid
    {k j : ℕ} (hj : j ≤ k) :
    (j : ℝ) / (k : ℝ) ∈ normalizedGrid k := by
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩

/-- A finite normalized grid approximates every point of `[0, 1]`. -/
theorem normalizedGrid_approx
    {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ j : ℕ, j ≤ k ∧
      |x - (j : ℝ) / (k : ℝ)| ≤ 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  let y : ℝ := (k : ℝ) * x
  let j : ℕ := ⌊y⌋₊
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hyk : y ≤ (k : ℝ) := by
    dsimp [y]
    nlinarith [mul_le_mul_of_nonneg_left hx1 (Nat.cast_nonneg k)]
  have hjle : j ≤ k := by
    dsimp [j]
    exact Nat.floor_le_of_le hyk
  have hj_lower : (j : ℝ) ≤ y := by
    dsimp [j]
    exact Nat.floor_le hy0
  have hy_upper : y < (j : ℝ) + 1 := by
    dsimp [j]
    exact Nat.lt_floor_add_one y
  have h_lower : (j : ℝ) / (k : ℝ) ≤ x := by
    apply (div_le_iff₀ hkR).2
    simpa [y, mul_comm] using hj_lower
  have hupper' : x < ((j : ℝ) + 1) / (k : ℝ) := by
    apply (lt_div_iff₀ hkR).2
    simpa [y, mul_comm] using hy_upper
  have h_upper : x < (j : ℝ) / (k : ℝ) + 1 / (k : ℝ) := by
    calc
      x < ((j : ℝ) + 1) / (k : ℝ) := hupper'
      _ = (j : ℝ) / (k : ℝ) + 1 / (k : ℝ) := by
        field_simp [ne_of_gt hkR]
  refine ⟨j, hjle, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr h_lower)]
  linarith

end

end DkMath.CosmicFormula.Projection
