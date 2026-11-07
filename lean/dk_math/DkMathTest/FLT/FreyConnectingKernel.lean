/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelCertificate

#print "file: DkMathTest.FLT.FreyConnectingKernel"

namespace FreyConnectingKernelTest
abbrev R := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def projection : (R × R) →ₗ[R] R := LinearMap.snd R R R
private def shear (t : R) (z : R × R) : R × R := (z.1 + t * z.2, z.2)
-- Quotient projection fixed does NOT imply original action fixed.
example (t : R) (z : R × R) : projection (shear t z) = projection z := rfl
example : shear 1 (0, 1) ≠ (0, 1) := by decide

private def kernelEquiv : R ≃ₗ[R] LinearMap.ker projection where
  toFun r := ⟨(r, 0), rfl⟩
  invFun z := z.val.1
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    change (z.val.1, 0) = z.val
    apply Prod.ext
    · rfl
    · exact (show z.val.2 = 0 from z.property).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- A genuine linear kernel equivalence keeps the SAME values and exact orders.
example (r : R) : (kernelEquiv r).val = (r, 0) := rfl
example : Nat.card (LinearMap.ker projection) = 5 :=
  (Nat.card_congr kernelEquiv.toEquiv).symm.trans (Nat.card_zmod 5)
private theorem generator_order : addOrderOf (kernelEquiv 1) = 5 := by
  exact (kernelEquiv.toAddEquiv.addOrderOf_eq 1).trans
    (addOrderOf_eq_prime_iff.mpr ⟨by decide, by decide⟩)
example : Nat.card (AddSubgroup.zmultiples (kernelEquiv 1)) = 5 :=
  (Nat.card_zmultiples _).trans generator_order

-- An order5 cyclic subgroup does NOT force the entire kernel to have cardinal5.
example : LinearMap.ker (0 : (R × R) →ₗ[R] R) = ⊤ := LinearMap.ker_zero
example : Nat.card (R × R) = 25 := by
  rw [Nat.card_prod, Nat.card_zmod]
example : Nat.card (AddSubgroup.zmultiples ((1, 0) : R × R)) = 5 := by
  rw [Nat.card_zmultiples]
  exact addOrderOf_eq_prime_iff.mpr ⟨by decide, by decide⟩
end FreyConnectingKernelTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_all_invariant
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_action_trivial
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientInvariantEquiv
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH0Projection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH0Projection_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1CoefficientMap
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1CoefficientKernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_range
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingToKernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingKernelEquiv
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.invariantConnectingKernelEquiv
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.pointClass_killed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_killed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCosetH0_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement_val
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_cyclic_card
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_coset
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_prime_power_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_positive_profile
#print axioms DkMath.FLT.Frey.Source.residual_exists_prime_cyclic_coefficient_kernel
