/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.LinearAlgebra.Matrix.Adjugate

#print "file: DkMath.Lib.NumberTheory.FiniteFreeLatticeLanding"

/-!
# Integral matrix lattice landing

The image of an integer matrix with nonzero determinant is characterized by
divisibility of every adjugate-product coordinate. No scalar norm criterion
or finite-free algebra structure is assumed.
-/

namespace DkMath.Lib.NumberTheory

open Matrix

/-- Exact integral image criterion in the nonzero-determinant region. -/
theorem exists_mulVec_eq_iff_adjugate_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (v : ι → ℤ) (hdet : M.det ≠ 0) :
    (∃ w : ι → ℤ, M *ᵥ w = v) ↔
      ∀ i, M.det ∣ (M.adjugate *ᵥ v) i := by
  constructor
  · rintro ⟨w, rfl⟩ i
    refine ⟨w i, ?_⟩
    simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec,
      Pi.smul_apply, smul_eq_mul]
  · intro h
    choose w hw using h
    have hv : M.adjugate *ᵥ v = M.det • w := by
      funext i
      exact hw i
    have heq : M.det • v = M.det • (M *ᵥ w) := by
      calc
        M.det • v = M *ᵥ (M.adjugate *ᵥ v) := by
          rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
        _ = M.det • (M *ᵥ w) := by rw [hv, mulVec_smul]
    refine ⟨w, ?_⟩
    funext i
    exact (mul_left_cancel₀ hdet (congrFun heq i)).symm

end DkMath.Lib.NumberTheory
