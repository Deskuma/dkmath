/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinNumeratorFunctionRankAudit
import Mathlib.Tactic

/-!
# Finite evaluation rank for the symmetric Mellin numerator

For an arbitrary finite family of squared-distinct coordinates, this module
constructs real evaluation parameters whose symmetric-numerator evaluation
matrix has nonzero determinant.  The construction is a direct induction on
the family size: the new final row is left variable, and a cofactor
contradiction invokes the already proved C1L function-rank theorem.

The parameters are existence witnesses for an arbitrary finite family; no Xi
zero carrier or actual Xi-window representative is used.  The numerator is
used first, so determinant nonvanishing automatically excludes `τ = 0`.
The corresponding bare Mellin-kernel determinant then follows by exact
nonzero row scaling.

Finite evaluation rank here is not the C2 actual-window transfer and does not
authorize any later off-critical or Guinand--Weil construction.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open scoped BigOperators Matrix

private theorem mellinSymmetricNumerator_eval_exists_induction
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
      (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)) :
    ∃ τ : Fin n → ℝ,
      Matrix.det ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  induction n with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      simp
  | succ n ih =>
      let z0 : Fin n → ℂ := fun j => z j.castSucc
      have hq0 : ∀ j, z0 j ^ 2 ≠ 0 := by
        intro j
        exact hq j.castSucc
      have hpair0 : Pairwise (fun i j => z0 i ^ 2 ≠ z0 j ^ 2) := by
        intro i j hij
        apply hpair
        intro hcast
        exact hij ((Fin.castSucc_injective n) hcast)
      obtain ⟨τ0, hdet0⟩ := ih hq0 hpair0
      let A : Matrix (Fin n) (Fin n) ℂ :=
        fun i j => mellinSymmetricNumerator (τ0 i) (z0 j)
      have hdetA : A.det ≠ 0 := by
        simpa [A] using hdet0
      let E : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun t i j =>
        Fin.lastCases
          (mellinSymmetricNumerator t (z j))
          (fun i => mellinSymmetricNumerator (τ0 i) (z j)) i
      let cofactor : Fin (n + 1) → ℂ := fun j =>
        (-1 : ℂ) ^ ((Fin.last n).val + j.val) *
          ((E 0).submatrix (Fin.last n).succAbove j.succAbove).det
      have hlast_minor :
          (E 0).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
        ext i j
        simp [E, A, z0, Fin.succAbove_last]
      have hcofactor_last : cofactor (Fin.last n) ≠ 0 := by
        simp only [cofactor]
        have hsign : (-1 : ℂ) ^ (n + n) = 1 := by
          rw [show n + n = 2 * n by omega, pow_mul]
          simp
        rw [show (Fin.last n).val = n by rfl, hsign, hlast_minor]
        simpa using hdetA
      have hminor (t : ℝ) (j : Fin (n + 1)) :
          (E t).submatrix (Fin.last n).succAbove j.succAbove =
            (E 0).submatrix (Fin.last n).succAbove j.succAbove := by
        ext i k
        simp [E, Fin.succAbove_last]
      have hex : ∃ t : ℝ, (E t).det ≠ 0 := by
        by_contra h
        push Not at h
        have hzero : ∀ t : ℝ,
            ∑ j, cofactor j * mellinSymmetricNumerator t (z j) = 0 := by
          intro t
          have hdet_t : (E t).det = 0 := h t
          have hexpand :
              (E t).det =
                ∑ j, (-1 : ℂ) ^ ((Fin.last n).val + j.val) *
                  (E t) (Fin.last n) j *
                  ((E t).submatrix (Fin.last n).succAbove j.succAbove).det := by
            simpa [E, Fin.lastCases_last] using
              (Matrix.det_succ_row (E t) (Fin.last n))
          calc
            ∑ j, cofactor j * mellinSymmetricNumerator t (z j) =
                ∑ j, (-1 : ℂ) ^ ((Fin.last n).val + j.val) *
                  (E t) (Fin.last n) j *
                  ((E t).submatrix (Fin.last n).succAbove j.succAbove).det := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    simp only [cofactor]
                    rw [hminor t j]
                    simp [E, Fin.lastCases_last]
                    ring
            _ = (E t).det := hexpand.symm
            _ = 0 := hdet_t
        have hcofactor_zero :=
          mellinSymmetricNumerator_combination_eq_zero_imp_coeff_zero
            hq hpair cofactor hzero
        exact hcofactor_last (hcofactor_zero (Fin.last n))
      obtain ⟨t, ht⟩ := hex
      let τ : Fin (n + 1) → ℝ :=
        Fin.lastCases t (fun i => τ0 i)
      refine ⟨τ, ?_⟩
      have hEτ : E t =
          ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
        funext i j
        refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [E, τ]
      rw [hEτ] at ht
      exact ht

/-- Every finite nonzero, squared-distinct coordinate family admits real
evaluation parameters with an invertible symmetric-numerator matrix. -/
theorem exists_mellinSymmetricNumerator_evaluation_det_ne_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)) :
    ∃ τ : Fin n → ℝ,
      Matrix.det ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  exact mellinSymmetricNumerator_eval_exists_induction hq hpair

/-- A nonzero determinant of a symmetric-numerator evaluation matrix forces
every evaluation parameter to be nonzero, because the numerator vanishes at
`τ = 0`. -/
theorem evaluation_det_ne_zero_imp_parameters_ne_zero
    {n : ℕ} {z : Fin n → ℂ} {τ : Fin n → ℝ}
    (hdet :
      Matrix.det ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    ∀ i, τ i ≠ 0 := by
  intro i hi
  apply hdet
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  rw [hi, mellinSymmetricNumerator_zero]

/-- A nonzero determinant of an evaluation matrix forces the evaluation
parameters to be injective: equal parameters would give equal rows. -/
theorem evaluation_det_ne_zero_imp_parameters_injective
    {n : ℕ} {z : Fin n → ℂ} {τ : Fin n → ℝ}
    (hdet :
      Matrix.det ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    Function.Injective τ := by
  intro i j hij
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp only [hij]

/-- The numerator finite-evaluation theorem transfers to the bare Mellin
kernel by the exact nonzero row scaling supplied by
`mellinSymmetricNumerator_eq_kernel_mul`. -/
theorem exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)) :
    ∃ τ : Fin n → ℝ,
      (∀ i, τ i ≠ 0) ∧
      Function.Injective τ ∧
      Matrix.det ((fun i j => complexExpSecondDifferenceKernel (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  obtain ⟨τ, hdet⟩ := exists_mellinSymmetricNumerator_evaluation_det_ne_zero hq hpair
  have hτ := evaluation_det_ne_zero_imp_parameters_ne_zero hdet
  have hinj := evaluation_det_ne_zero_imp_parameters_injective hdet
  let K : Matrix (Fin n) (Fin n) ℂ :=
    fun i j => complexExpSecondDifferenceKernel (τ i) (z j)
  have hmatrix :
      ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) =
      (Matrix.diagonal (fun i => (τ i : ℂ) ^ 2) :
          Matrix (Fin n) (Fin n) ℂ) * K := by
    ext i j
    simpa [K, Matrix.mul_apply, Matrix.diagonal] using
      (mellinSymmetricNumerator_eq_kernel_mul (hτ i) (z j))
  have hscale : ∏ i, (τ i : ℂ) ^ 2 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hτ i))
  have hfactor :
      Matrix.det ((fun i j => mellinSymmetricNumerator (τ i) (z j)) :
        Matrix (Fin n) (Fin n) ℂ) =
        (∏ i, (τ i : ℂ) ^ 2) * K.det := by
    rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
  have hK : K.det ≠ 0 := by
    intro hKzero
    apply hdet
    rw [hfactor, hKzero, mul_zero]
  exact ⟨τ, hτ, hinj, by simpa [K] using hK⟩

end DkMath.RH.CFBRCProjection
