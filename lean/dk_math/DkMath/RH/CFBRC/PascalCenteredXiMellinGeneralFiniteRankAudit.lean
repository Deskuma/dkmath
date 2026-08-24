/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteTauLowRankAudit
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# General finite Mellin coefficient rank audit

This module isolates the algebraic part of the general finite-orbit problem.
The first even Mellin jet coefficient matrix is a row- and column-scaled
transpose of a Vandermonde matrix in the squared coordinates.  Thus nonzero
pairwise-distinct squared coordinates give coefficient rank for every finite
index `Fin n`.

This is deliberately only the coefficient-rank statement.  It does not turn
jet rank into finite nonzero-`τ` evaluation rank: that analytic evaluation
bridge remains an explicit boundary of the current API.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators

/-- The coefficient matrix of the first `n` even Mellin jets, indexed by jet
order in the rows and squared coordinates in the columns. -/
def mellinJetCoefficientMatrix {n : ℕ} (q : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun r j => 2 * q j ^ (r.1 + 1) / (Nat.factorial (2 * r.1 + 2) : ℂ)

/-- The general squared-coordinate Mellin jet coefficient matrix is nonzero in
determinant whenever all squared coordinates are nonzero and pairwise
distinct. -/
theorem mellinJetCoefficientMatrix_det_ne_zero {n : ℕ} {q : Fin n → ℂ}
    (hq : ∀ j, q j ≠ 0)
    (hpair : Pairwise (fun i j => q i ≠ q j)) :
    (mellinJetCoefficientMatrix q).det ≠ 0 := by
  let a : Fin n → ℂ := fun r => 2 / (Nat.factorial (2 * r.1 + 2) : ℂ)
  let b : Fin n → ℂ := fun j => q j
  have hinj : Function.Injective q := by
    intro i j hij
    by_contra hne
    exact hpair hne hij
  have hmatrix : mellinJetCoefficientMatrix q =
      Matrix.diagonal a * Matrix.transpose (Matrix.vandermonde q) *
        Matrix.diagonal b := by
    ext r j
    simp [mellinJetCoefficientMatrix, a, b, Matrix.mul_apply, Matrix.diagonal]
    ring_nf
  have hv : (Matrix.vandermonde q).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose, Matrix.det_diagonal]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro r hr
      apply div_ne_zero
      · norm_num
      · exact_mod_cast Nat.factorial_ne_zero (2 * r.1 + 2)
    · simpa using hv
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hq j

end DkMath.RH.CFBRCProjection
