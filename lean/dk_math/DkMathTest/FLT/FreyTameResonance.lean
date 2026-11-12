/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTameResonance

#print "file: DkMathTest.FLT.FreyTameResonance"

namespace FreyTameResonanceTest
open DkMath.Lib.Algebra.PrimeOrderResonance
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def z : Multiplicative (ZMod 5) := Multiplicative.ofAdd 1
private theorem exact_order : orderOf z = 5 := by
  change addOrderOf (1 : ZMod 5) = 5
  exact addOrderOf_eq_prime_iff.mpr ⟨by decide, by decide⟩

-- Actual positive and negative residue branches preserve the SAME element.
example : z ^ 11 = z := (pow_eq_self_iff exact_order).mpr (by decide)
example : z ^ 19 = z⁻¹ := pow_eq_inv exact_order (by decide)
example : z ^ 19 ≠ z := pow_ne_self_of_negative (by decide : 2 < 5) exact_order (by decide)
-- Outside the positive branch fixedness fails; no conjugacy invariance is assumed.
example : z ^ 2 ≠ z := by
  intro h
  have hbad := (pow_eq_self_iff exact_order).mp h
  exact (by decide : (2 : ZMod 5) ≠ 1) hbad
-- The p>2 guard is essential: a nontrivial order-two element equals its inverse.
example : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide

private def reduction : Multiplicative (ZMod 25) →* Multiplicative (ZMod 5) :=
  (ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)).toAddMonoidHom.toMultiplicative
private def descended : ((Multiplicative (ZMod 25)) ⧸ reduction.ker) →* Multiplicative (ZMod 5) :=
  QuotientGroup.lift reduction.ker reduction le_rfl
-- Canonical descent retains both the nontrivial value and values at different representatives.
example : descended (QuotientGroup.mk (Multiplicative.ofAdd (1 : ZMod 25))) = z := by
  change reduction (Multiplicative.ofAdd 1) = z
  decide
example : descended (QuotientGroup.mk (Multiplicative.ofAdd (6 : ZMod 25))) = z := by
  change reduction (Multiplicative.ofAdd 6) = z
  decide
example : orderOf (descended (QuotientGroup.mk (Multiplicative.ofAdd (6 : ZMod 25)))) = 5 := by
  change orderOf (reduction (Multiplicative.ofAdd 6)) = 5
  have h : reduction (Multiplicative.ofAdd 6) = z := by decide
  rw [h, exact_order]
end FreyTameResonanceTest

#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.conjugate
#print axioms DkMath.Lib.NumberTheory.ValuationWildRigidity.inertiaWild_normal
#print axioms DkMath.FLT.Frey.Source.wildInertiaSubgroup_normal
#print axioms DkMath.FLT.Frey.Source.tameInertiaQuotient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_range
#print axioms DkMath.FLT.Frey.Source.tameInertia_frobenius_power
#print axioms DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_self_iff
#print axioms DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_inv
#print axioms DkMath.Lib.Algebra.PrimeOrderResonance.inv_ne_self
#print axioms DkMath.Lib.Algebra.PrimeOrderResonance.pow_ne_self_of_negative
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_character_nontrivial
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_resonant_profile
#print axioms DkMath.FLT.Frey.Source.residual_exists_resonant_tame_character
