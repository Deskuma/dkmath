/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConditionalCofixedExclusion

#print "file: DkMathTest.FLT.FreyConditionalCofixedExclusion"

namespace FreyTateUnipotenceTest
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A nilpotent scalar over a finite nonreduced ring cannot be cancelled.
example : ((6 : ZMod 25) - 1) ^ 2 = 0 ∧ (6 : ZMod 25) ≠ 1 := by decide

-- Over Z_5 a unipotent action can still have an actual nonzero upper-right entry.
private noncomputable def U : Matrix (Fin 2) (Fin 2) ℤ_[5] := !![1, 1; 0, 1]
example : (U - 1) ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

example : U ≠ 1 := by
  intro h
  have he : (1 : ℤ_[5]) = 0 := by simpa [U] using congrArg (fun M => M 0 1) h
  exact one_ne_zero he
end FreyTateUnipotenceTest

-- Kernel axiom reports for all new production declarations.
#print axioms DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_product_zero
#print axioms DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_square_zero
#print axioms DkMath.FLT.Frey.Source.prime_power_inertia_difference_square_zero
#print axioms DkMath.FLT.Frey.Source.tate_inertia_difference_square_zero
#print axioms DkMath.FLT.Frey.Source.residualTateActionMatrix_inertia_square_zero
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter_inertia_eq_one
#print axioms DkMath.FLT.Frey.Source.residualFinite_inertia_absorbs_at_bad
#print axioms DkMath.FLT.Frey.Source.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
#print axioms DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_failure
#print axioms DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_counterexample
#print axioms DkMath.FLT.Frey.Source.residual_hno_of_class_vanishing_and_resonant_absorption
