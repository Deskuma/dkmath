/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralNumeratorJetAudit
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic

/-!
# Direct function rank for the symmetric Mellin numerator

This module closes the direct, zero-independent function-rank step for the
family `τ ↦ mellinSymmetricNumerator τ z`.  An identically zero finite linear
combination is divided successively by the even powers of `τ`; the previously
proved general-jet limit extracts every coefficient row.  The resulting
matrix equation is discharged by the already established Vandermonde
determinant theorem.

This is an extensional function-rank statement only.  It does not choose an
actual Xi zero, prove a finite nonzero-`τ` evaluation bridge, or enter the
later GWSS stages.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators
open scoped Matrix

private theorem mellinSymmetricNumerator_combination_lower_part_eq_zero
    {n : ℕ} (z c : Fin n → ℂ) (m : ℕ)
    (hlower : ∀ r < m,
      ∑ j, c j * mellinSymmetricNumeratorJetCoeff r (z j) = 0)
    (τ : ℝ) :
    ∑ j, c j *
        (∑ r ∈ Finset.range m,
          mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2)) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r hr
  have hrlt : r < m := Finset.mem_range.mp hr
  calc
    ∑ x, c x *
        (mellinSymmetricNumeratorJetCoeff r (z x) * (τ : ℂ) ^ (2 * r + 2)) =
        (∑ x, c x * mellinSymmetricNumeratorJetCoeff r (z x)) *
          (τ : ℂ) ^ (2 * r + 2) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = 0 := by rw [hlower r hrlt, zero_mul]

/-- The next even Mellin jet row vanishes once all preceding rows vanish. -/
theorem mellinSymmetricNumerator_combination_nextJet_eq_zero
    {n : ℕ} (z c : Fin n → ℂ) (m : ℕ)
    (hzero : ∀ τ : ℝ,
      ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0)
    (hlower : ∀ r < m,
      ∑ j, c j * mellinSymmetricNumeratorJetCoeff r (z j) = 0) :
    ∑ j, c j * mellinSymmetricNumeratorJetCoeff m (z j) = 0 := by
  let L : Filter ℝ := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hquot : Tendsto
      (fun τ : ℝ =>
        ∑ j, c j *
          ((mellinSymmetricNumerator τ (z j) -
            ∑ r ∈ Finset.range m,
              mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2)) /
            (τ : ℂ) ^ (2 * m + 2)))
      L (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => (0 : ℂ)) L (nhds 0) :=
      tendsto_const_nhds
    apply hconst.congr'
    filter_upwards [self_mem_nhdsWithin] with τ _
    have hnum :
        ∑ j, c j *
            (mellinSymmetricNumerator τ (z j) -
              ∑ r ∈ Finset.range m,
                mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      change (∑ j, c j * mellinSymmetricNumerator τ (z j)) -
        (∑ j, c j *
          (∑ r ∈ Finset.range m,
            mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2))) = 0
      rw [hzero τ, mellinSymmetricNumerator_combination_lower_part_eq_zero z c m hlower τ]
      simp
    calc
      0 =
          (∑ j, c j *
            (mellinSymmetricNumerator τ (z j) -
              ∑ r ∈ Finset.range m,
                mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2))) /
            (τ : ℂ) ^ (2 * m + 2) := by rw [hnum, zero_div]
      _ = ∑ j, c j *
          ((mellinSymmetricNumerator τ (z j) -
            ∑ r ∈ Finset.range m,
              mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2)) /
            (τ : ℂ) ^ (2 * m + 2)) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j hj
              ring
  have hsum : Tendsto
      (fun τ : ℝ =>
        ∑ j, c j *
          ((mellinSymmetricNumerator τ (z j) -
            ∑ r ∈ Finset.range m,
              mellinSymmetricNumeratorJetCoeff r (z j) * (τ : ℂ) ^ (2 * r + 2)) /
            (τ : ℂ) ^ (2 * m + 2)))
      L (nhds (∑ j, c j * mellinSymmetricNumeratorJetCoeff m (z j))) := by
    apply tendsto_finsetSum
    intro j hj
    simpa only [mul_assoc] using
      (tendsto_const_nhds.mul
        (tendsto_mellinSymmetricNumerator_generalJet m (z j)))
  exact tendsto_nhds_unique hsum hquot

private theorem mellinSymmetricNumerator_combination_allJet_eq_zero
    {n : ℕ} (z c : Fin n → ℂ)
    (hzero : ∀ τ : ℝ,
      ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0) :
    ∀ m : ℕ, m < n →
      ∑ j, c j * mellinSymmetricNumeratorJetCoeff m (z j) = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm
      apply mellinSymmetricNumerator_combination_nextJet_eq_zero z c m hzero
      intro r hr
      exact ih r hr (lt_trans hr hm)

/-! The direct annihilation theorem is the public C1L load-bearing result. -/

/-- An identically zero finite combination of symmetric Mellin numerators has
all coefficients zero when the squared coordinates are nonzero and pairwise
distinct.

The proof extracts all finite even jet rows at `τ = 0`, identifies them with
the previously audited coefficient matrix, and applies its nonzero
determinant.  No Xi zero or finite evaluation point is selected here. -/
theorem mellinSymmetricNumerator_combination_eq_zero_imp_coeff_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2))
    (c : Fin n → ℂ)
    (hzero : ∀ τ : ℝ,
      ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0) :
    ∀ j, c j = 0 := by
  have hall : ∀ r : Fin n,
      ∑ j, c j * mellinSymmetricNumeratorJetCoeff r.1 (z j) = 0 := by
    intro r
    exact mellinSymmetricNumerator_combination_allJet_eq_zero z c hzero r.1 r.isLt
  let M : Matrix (Fin n) (Fin n) ℂ :=
    mellinJetCoefficientMatrix (fun j => (z j) ^ 2)
  have hmul : M *ᵥ c = 0 := by
    funext r
    change (∑ j, M r j * c j) = 0
    simpa [M, mul_comm,
      mellinSymmetricNumeratorJetCoeff_eq_coefficientMatrix z r] using hall r
  have hdet : M.det ≠ 0 := by
    exact mellinJetCoefficientMatrix_det_ne_zero hq hpair
  have hc : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  intro j
  exact congrFun hc j

end DkMath.RH.CFBRCProjection
