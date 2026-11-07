/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWildInertia

#print "file: DkMathTest.FLT.FreyWildInertia"

namespace FreyWildInertiaTest
open DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
abbrev R := ZMod 25
private def shear (t : R) : Module.End R (R × R) where
  toFun x := (x.1 + t * x.2, x.2)
  map_add' x y := by
    apply Prod.ext
    · change x.1 + y.1 + t * (x.2 + y.2) = (x.1 + t * x.2) + (y.1 + t * y.2)
      ring
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · change c * x.1 + t * (c * x.2) = c * (x.1 + t * x.2)
      ring
    · rfl
private def rho : Representation R (Multiplicative R) (R × R) where
  toFun t := shear (Multiplicative.toAdd t)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp [shear]
  map_mul' t u := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change x.1 + (Multiplicative.toAdd t + Multiplicative.toAdd u) * x.2 =
        (x.1 + Multiplicative.toAdd u * x.2) + Multiplicative.toAdd t * x.2
      ring
    · rfl
private theorem prod_zero (t u : Multiplicative R) : (rho t - 1) * (rho u - 1) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> simp [rho, shear, Module.End.mul_apply]

-- The exact power formula retains the SAME point and SAME acting element.
example : rho ((Multiplicative.ofAdd (1 : R)) ^ 5) (0, 1) - (0, 1) = (5, 0) := by
  rw [difference_pow rho prod_zero]
  decide

-- Exponent 25 kills this point and supplies its actual action period.
example : rho ((Multiplicative.ofAdd (1 : R)) ^ 25) (0, 1) = (0, 1) := by
  apply fixed_by_pow_of_killed rho prod_zero
  decide

-- A point killed by 5 has period 5, even though the acting shear is nontrivial.
example : rho ((Multiplicative.ofAdd (1 : R)) ^ 5) (0, 5) = (0, 5) := by
  apply fixed_by_pow_of_killed rho prod_zero
  decide
example : rho (Multiplicative.ofAdd (1 : R)) (0, 5) ≠ (0, 5) := by decide

-- Unipotence alone does not remove action: the wild rigidity guard is essential.
example : rho ((Multiplicative.ofAdd (1 : R)) ^ 5) (0, 1) ≠ (0, 1) := by decide
example : rho ((Multiplicative.ofAdd (1 : R)) ^ 0) (0, 1) - (0, 1) = (0, 0) := by
  rw [difference_pow rho prod_zero, zero_nsmul]
  rfl
end FreyWildInertiaTest

#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.valuation_lt_iff_div_mem_nonunits
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.isWildAt_of_forall_mem_nonunits
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.valuation_apply
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.mul
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.inv
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.isWildAt_iff
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.wildSubgroup
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.pow
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.fixed_of_unit_period
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.fixed_of_coprime_period
#print axioms DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_pow
#print axioms DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.fixed_by_pow_of_killed
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_fixed_of_wild_coprime_period
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_fixed_of_wild_coprime_period
#print axioms DkMath.FLT.Frey.Source.wildInertiaSubgroup
#print axioms DkMath.FLT.Frey.Source.prime_power_wild_inertia_fixed
#print axioms DkMath.FLT.Frey.Source.frobenius_conjugate_error_wild
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_frobenius_character_power
#print axioms DkMath.FLT.Frey.Source.residual_exists_tame_inertia_character
