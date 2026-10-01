/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.LevelSet

namespace DkMath.NumberGeometry
open scoped InnerProductSpace
noncomputable section

/-!
# Radical square-mass decomposition

This module isolates the algebraic cross term created by a radical component.
Orthogonality removes that term and yields a base-field square-mass landing;
no integrality or number-theoretic conclusion is built into the API.
-/

/-- The norm square of a radical sum, including its inner-product cross term. -/
theorem norm_sq_add_sqrt_smul
    (u v : Point) {m : ℝ} (hm : 0 ≤ m) :
    ‖u + Real.sqrt m • v‖ ^ 2 =
      ‖u‖ ^ 2
        + m * ‖v‖ ^ 2
        + 2 * Real.sqrt m * ⟪u, v⟫_ℝ := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg m), mul_pow,
    Real.sq_sqrt hm]
  ring

/-- Orthogonality removes the radical cross term from the norm square. -/
theorem norm_sq_add_sqrt_smul_of_inner_eq_zero
    (u v : Point) {m : ℝ} (hm : 0 ≤ m)
    (huv : ⟪u, v⟫_ℝ = 0) :
    ‖u + Real.sqrt m • v‖ ^ 2 =
      ‖u‖ ^ 2 + m * ‖v‖ ^ 2 := by
  rw [norm_sq_add_sqrt_smul u v hm, huv]
  ring

/-- Pair mass decomposes into base, radical, and inner-product terms. -/
theorem pairMass_radical
    (A u v : Point) {m : ℝ} (hm : 0 ≤ m) :
    pairMass A (A + u + Real.sqrt m • v) =
      ‖u‖ ^ 2
        + m * ‖v‖ ^ 2
        + 2 * Real.sqrt m * ⟪u, v⟫_ℝ := by
  have hgap : pairVec A (A + u + Real.sqrt m • v) =
      u + Real.sqrt m • v := by
    simp only [pairVec, sub_eq_add_neg]
    abel
  rw [pairMass, hgap]
  exact norm_sq_add_sqrt_smul u v hm

/-- An orthogonal radical component gives a square-mass landing. -/
theorem pairMass_radical_of_inner_eq_zero
    (A u v : Point) {m : ℝ} (hm : 0 ≤ m)
    (huv : ⟪u, v⟫_ℝ = 0) :
    pairMass A (A + u + Real.sqrt m • v) =
      ‖u‖ ^ 2 + m * ‖v‖ ^ 2 := by
  have hgap : pairVec A (A + u + Real.sqrt m • v) =
      u + Real.sqrt m • v := by
    simp only [pairVec, sub_eq_add_neg]
    abel
  rw [pairMass, hgap]
  exact norm_sq_add_sqrt_smul_of_inner_eq_zero u v hm huv

/-- The plus/minus radical conjugates differ by twice the odd cross term. -/
theorem pairMass_radical_conj_sub
    (A u v : Point) {m : ℝ} (hm : 0 ≤ m) :
    pairMass A (A + u + Real.sqrt m • v)
      - pairMass A (A + u - Real.sqrt m • v) =
    4 * Real.sqrt m * ⟪u, v⟫_ℝ := by
  have hplus := pairMass_radical A u v hm
  have hminus :
      pairMass A (A + u - Real.sqrt m • v) =
        ‖u‖ ^ 2 + m * ‖v‖ ^ 2 -
          2 * Real.sqrt m * ⟪u, v⟫_ℝ := by
    have hminus' := pairMass_radical A u (-v) hm
    simpa [sub_eq_add_neg, smul_neg, norm_neg, real_inner_smul_right] using hminus'
  rw [hplus, hminus]
  ring

/-- Equal mass of this positive radical conjugate pair is equivalent to orthogonality. -/
theorem pairMass_radical_conj_eq_iff_inner_eq_zero
    (A u v : Point) {m : ℝ} (hm : 0 < m) :
    pairMass A (A + u + Real.sqrt m • v) =
      pairMass A (A + u - Real.sqrt m • v) ↔
    ⟪u, v⟫_ℝ = 0 := by
  have hsqrt : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  constructor
  · intro hmass
    have hzero : 4 * Real.sqrt m * ⟪u, v⟫_ℝ = 0 := by
      calc
        4 * Real.sqrt m * ⟪u, v⟫_ℝ =
            pairMass A (A + u + Real.sqrt m • v)
              - pairMass A (A + u - Real.sqrt m • v) :=
          (pairMass_radical_conj_sub A u v hm.le).symm
        _ = 0 := sub_eq_zero.mpr hmass
    exact (mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (by norm_num) hsqrt)
  · intro huv
    have hdiff := pairMass_radical_conj_sub A u v hm.le
    rw [huv] at hdiff
    exact sub_eq_zero.mp (by simpa using hdiff)

/-- An orthogonal radical point belongs to its predicted square-mass level set. -/
theorem mem_massLevelSet_radical_of_inner_eq_zero
    (A u v : Point) {m rho : ℝ} (hm : 0 ≤ m)
    (huv : ⟪u, v⟫_ℝ = 0)
    (hrho : rho = ‖u‖ ^ 2 + m * ‖v‖ ^ 2) :
    A + u + Real.sqrt m • v ∈ MassLevelSet A rho := by
  change pairMass A (A + u + Real.sqrt m • v) = rho
  rw [pairMass_radical_of_inner_eq_zero A u v hm huv, hrho]

end
end DkMath.NumberGeometry
