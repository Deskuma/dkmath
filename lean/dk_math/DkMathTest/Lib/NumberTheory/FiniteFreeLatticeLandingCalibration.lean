/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FiniteFreeLatticeLanding
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

#print "file: DkMathTest.Lib.NumberTheory.FiniteFreeLatticeLandingCalibration"

namespace DkMathTest.FiniteFreeLatticeLanding

open Matrix DkMath.Lib.NumberTheory

def diagonal : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 3]
def mixed : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 2]
def singular : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 0]

/-- The diagonal criterion reconstructs an integral preimage. -/
theorem diagonal_landing : ∃ w, diagonal *ᵥ w = ![4, 9] := by
  apply (exists_mulVec_eq_iff_adjugate_dvd diagonal ![4, 9]
    (by norm_num [diagonal, det_fin_two])).mpr
  intro i
  fin_cases i <;> norm_num [diagonal, adjugate_fin_two, det_fin_two, mulVec, dotProduct]

/-- A non-diagonal matrix passes both adjugate-coordinate tests. -/
theorem mixed_landing : ∃ w, mixed *ᵥ w = ![4, 5] := by
  apply (exists_mulVec_eq_iff_adjugate_dvd mixed ![4, 5]
    (by norm_num [mixed, det_fin_two])).mpr
  intro i
  fin_cases i <;> norm_num [mixed, adjugate_fin_two, det_fin_two, mulVec, dotProduct]

/-- One failed coordinate suffices to exclude image landing. -/
theorem mixed_coordinate_failure : ¬ mixed.det ∣ (mixed.adjugate *ᵥ ![1, 0]) 0 := by
  norm_num [mixed, adjugate_fin_two, det_fin_two, mulVec, dotProduct]

theorem mixed_not_landing : ¬ ∃ w, mixed *ᵥ w = ![1, 0] := by
  intro h
  exact mixed_coordinate_failure
    ((exists_mulVec_eq_iff_adjugate_dvd mixed ![1, 0]
      (by norm_num [mixed, det_fin_two])).mp h 0)

/-- A nonzero singular matrix satisfies the coordinate condition for a vector
outside its image. Thus nonzero matrix is insufficient in the public theorem. -/
theorem singular_boundary :
    singular ≠ 0 ∧ singular.det = 0 ∧
      (∀ i, singular.det ∣ (singular.adjugate *ᵥ ![1, 0]) i) ∧
      ¬ ∃ w, singular *ᵥ w = ![1, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
    norm_num [singular] at this
  · norm_num [singular, det_fin_two]
  · intro i
    fin_cases i <;> norm_num [singular, adjugate_fin_two, det_fin_two, mulVec, dotProduct]
  · rintro ⟨w, hw⟩
    have := congrFun hw 0
    norm_num [singular, mulVec, dotProduct, Fin.sum_univ_two] at this
    omega

end DkMathTest.FiniteFreeLatticeLanding
