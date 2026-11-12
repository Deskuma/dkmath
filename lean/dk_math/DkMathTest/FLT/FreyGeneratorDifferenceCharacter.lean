/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageIntersectionGenerator
import DkMath.FLT.FreyInertiaDifferenceCharacter

#print "file: DkMathTest.FLT.FreyGeneratorDifferenceCharacter"

namespace FreyGeneratorCharacterTest
abbrev R := ZMod 25
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def H : AddSubgroup R := (ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)).toAddMonoidHom.ker
private def coordinate : ZMod (5 ^ 2) ≃+ (⊤ : AddSubgroup R) where
  toFun x := ⟨x, trivial⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
private theorem card_top : Nat.card (⊤ : AddSubgroup R) = 5 ^ 2 := by
  rw [← Nat.card_congr coordinate.toEquiv, Nat.card_zmod]
private theorem card_intersection : Nat.card ↥((⊤ : AddSubgroup R) ⊓ H) = 5 ^ 1 := by
  rw [top_inf_eq]
  let : DecidablePred (fun x : R => x ∈ H) := fun x => by
    change Decidable ((ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)) x = 0)
    infer_instance
  let : Fintype H := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  decide

example : addOrderOf ((QuotientAddGroup.mk' H) (1 : R)) = 5 := by
  have h := DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order_prime_power
    (⊤ : AddSubgroup R) H coordinate card_top (r := 1) (by decide) card_intersection
  exact h

example : H = AddSubgroup.zmultiples (5 : R) := by
  have h := DkMath.Lib.Algebra.CyclicIntersectionGenerator.intersection_eq_zmultiples
    (⊤ : AddSubgroup R) H coordinate card_top (r := 1) (by decide) card_intersection
  rw [top_inf_eq] at h
  change H = AddSubgroup.zmultiples ((5 : ℕ) • (1 : R)) at h
  rwa [show (5 : ℕ) • (1 : R) = (5 : R) by decide] at h

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

private theorem character_value (t : R) :
    Multiplicative.toAdd (DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character
      rho prod_zero (0, 1) (Multiplicative.ofAdd t)) = (t, 0) := by
  ext <;> simp [DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character, rho, shear]

example : addOrderOf (Multiplicative.toAdd
    (DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character rho prod_zero (0, 1)
      (Multiplicative.ofAdd (5 : R)))) = 5 := by
  rw [character_value]
  exact addOrderOf_eq_prime_iff.mpr ⟨by decide, by decide⟩
end FreyGeneratorCharacterTest

-- Kernel axiom reports for all new production declarations.
#print axioms DkMath.Lib.Algebra.CyclicIntersectionGenerator.zmultiples_generator
#print axioms DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order
#print axioms DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order_prime_power
#print axioms DkMath.Lib.Algebra.CyclicIntersectionGenerator.intersection_eq_zmultiples
#print axioms DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_fixed
#print axioms DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_mul
#print axioms DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character
#print axioms DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_conjugate
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.local_generator_order
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.smooth_intersection_generator
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_multiple_smooth_iff
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.local_generator_profile_of_not_smooth
#print axioms DkMath.FLT.Frey.Source.prime_power_inertia_difference_product_zero
#print axioms DkMath.FLT.Frey.Source.inertiaDifferenceCharacter
#print axioms DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_fixed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_apply
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_values_fixed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial
#print axioms DkMath.FLT.Frey.Source.residual_exists_nontrivial_inertia_quotient_character
