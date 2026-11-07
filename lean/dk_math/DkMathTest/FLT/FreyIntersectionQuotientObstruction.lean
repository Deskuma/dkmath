/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyIntersectionQuotientObstruction

#print "file: DkMathTest.FLT.FreyIntersectionQuotientObstruction"

namespace FreyIntersectionQuotientTest
abbrev G := ZMod 25 × ZMod 25
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def K : AddSubgroup G := (AddMonoidHom.snd (ZMod 25) (ZMod 25)).ker
private def residueFirst : G →+ ZMod 5 :=
  (ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)).toAddMonoidHom.comp
    (AddMonoidHom.fst (ZMod 25) (ZMod 25))
private def H : AddSubgroup G := residueFirst.ker
private def delta : G := (0, 5)

-- SAME delta is zero in G/H but has exact order5 in G/K.
example : (QuotientAddGroup.mk' H) delta = 0 :=
  (QuotientAddGroup.eq_zero_iff delta).mpr (by change residueFirst delta = 0; decide)

example : addOrderOf ((QuotientAddGroup.mk' K) delta) = 5 := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · rw [← map_nsmul, show (5 : ℕ) • delta = 0 by decide, map_zero]
  · intro he
    exact (by change delta.2 ≠ 0; decide : delta ∉ K) ((QuotientAddGroup.eq_zero_iff delta).mp he)

-- Concrete nontrivial intersection: K has25 elements, K intersect H has5, its image has5.
private theorem card_K : Nat.card K = 25 := by
  let : DecidablePred (fun x : G => x ∈ K) := fun x => by
    change Decidable (x.2 = 0)
    infer_instance
  let : Fintype K := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card_intersection : Nat.card ↥(K ⊓ H) = 5 := by
  let : DecidablePred (fun x : G => x ∈ K ⊓ H) := fun x => by
    change Decidable (x.2 = 0 ∧ residueFirst x = 0)
    infer_instance
  let : Fintype ↥(K ⊓ H) := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  decide
example : Nat.card (K.map (QuotientAddGroup.mk' H)) = 5 := by
  have h := DkMath.Lib.Algebra.FiniteSubgroupIntersection.card_intersection_mul_image K H
  rw [card_K, card_intersection] at h
  omega
end FreyIntersectionQuotientTest

-- Kernel axiom reports for all selected production roots.
#print axioms DkMath.Lib.Algebra.FiniteSubgroupIntersection.intersectionKerEquiv
#print axioms DkMath.Lib.Algebra.FiniteSubgroupIntersection.card_intersection_mul_image
#print axioms DkMath.Lib.Algebra.FiniteSubgroupIntersection.prime_power_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.smoothIntersection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.localComponentImage
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile_of_not_smooth
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_finite
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.intersection_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.difference_component_zero
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.finite_quotient_witness
#print axioms DkMath.FLT.Frey.Source.residual_exists_intersection_quotient_obstruction
