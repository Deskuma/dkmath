/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInertiaCharacterFiniteImage

#print "file: DkMathTest.FLT.FreyFiniteInertiaCharacter"

namespace FreyFiniteInertiaCharacterTest
open DkMath.Lib.Algebra.FinitePrimePowerCharacter
private def five : ZMod 25 →+ ZMod 25 where
  toFun x := 5 * x
  map_zero' := by simp
  map_add' x y := mul_add _ x y
private def character := five.toMultiplicative

-- A genuine noninjective character: image size and kernel index are 5, not 25.
private theorem image_card : Nat.card character.range = 5 := by
  let : DecidablePred (fun x : Multiplicative (ZMod 25) => x ∈ character.range) := fun x => by
    change Decidable (∃ y : Multiplicative (ZMod 25), character y = x)
    infer_instance
  let : Fintype character.range := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  decide

example : Nat.card ((Multiplicative (ZMod 25)) ⧸ character.ker) = 5 :=
  (card_quotient_kernel character).trans image_card
example : character.ker.index = 5 := (Subgroup.index_ker character).trans image_card

-- The positive exponent is supplied by an actual nontrivial value; its exact value is 1.
example : ∃ s, s = 1 ∧ Nat.card character.range = 5 ^ s ∧ character.ker.index = 5 ^ s := by
  obtain ⟨s, _, _, hc, _, hi⟩ := nontrivial_image_profile character (by decide : Nat.Prime 5)
    (m := 2) (by change Nat.card (ZMod 25) = 5 ^ 2; rw [Nat.card_zmod]; decide)
    ⟨Multiplicative.ofAdd 1, by decide⟩
  have hs : s = 1 := by
    have hp : 5 ^ s = 5 ^ 1 := by simpa only [image_card, pow_one] using hc.symm
    exact (pow_right_injective₀ (by decide : 0 < (5 : ℕ)) (by decide : (5 : ℕ) ≠ 1)) hp
  exact ⟨s, hs, hc, hi⟩

-- Trivial characters permit exponent zero; positivity cannot be inferred from finiteness.
example : Nat.card ((1 : Multiplicative (ZMod 25) →* Multiplicative (ZMod 25)).range) = 5 ^ 0 := by
  rw [pow_zero]
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    exact ha.symm.trans hb
  · exact ⟨1⟩
end FreyFiniteInertiaCharacterTest

#print axioms DkMath.Lib.Algebra.FinitePrimePowerCharacter.card_quotient_kernel
#print axioms DkMath.Lib.Algebra.FinitePrimePowerCharacter.image_profile
#print axioms DkMath.Lib.Algebra.FinitePrimePowerCharacter.nontrivial_image_profile
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStageEquiv
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage_card
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_card
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientDiscreteTopology
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_orbit_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_action_continuous
#print axioms DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_kernel_isClopen
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedUpperQuotient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_apply
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_character_image_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_finite_profile
#print axioms DkMath.FLT.Frey.Source.residual_exists_finite_inertia_character
