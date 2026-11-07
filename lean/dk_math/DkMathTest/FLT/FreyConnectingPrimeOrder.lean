/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1PrimeOrder

#print "file: DkMathTest.FLT.FreyConnectingPrimeOrder"

namespace FreyConnectingPrimeOrderTest
open DkMath.Lib.RepresentationTheory
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def character : Multiplicative (ZMod 5) →* Multiplicative (ZMod 5) := MonoidHom.id _

-- ALL values are killed by5; this proves the cohomology class, not just one value, is killed.
private theorem class_killed : 5 • TrivialCharacterH1.cohomologyClass character = 0 := by
  have hc : 5 • TrivialCharacterH1.cocycle character = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change 5 • Multiplicative.toAdd g = 0
    exact (by decide : ∀ v : ZMod 5, 5 • v = 0) (Multiplicative.toAdd g)
  unfold TrivialCharacterH1.cohomologyClass
  rw [← map_nsmul, hc, map_zero]
example : addOrderOf (TrivialCharacterH1.cohomologyClass character) = 5 := by
  apply addOrderOf_eq_prime_iff.mpr
  exact ⟨class_killed, TrivialCharacterH1.class_ne_zero character
    ⟨Multiplicative.ofAdd 1, by decide⟩⟩

-- A single order5 value is insufficient: the identity character on ZMod25 has a class not killed by5.
private def higher : Multiplicative (ZMod 25) →* Multiplicative (ZMod 25) := MonoidHom.id _
example : addOrderOf (Multiplicative.toAdd (higher (Multiplicative.ofAdd 5))) = 5 := by
  exact addOrderOf_eq_prime_iff.mpr ⟨by decide, by decide⟩
example : 5 • TrivialCharacterH1.cohomologyClass higher ≠ 0 := by
  intro h
  have he := congrArg (fun a =>
    (groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (Multiplicative (ZMod 25)) (ZMod 25))).hom a
      (Additive.ofMul (Multiplicative.ofAdd 1))) h
  have hm : (groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (Multiplicative (ZMod 25)) (ZMod 25))).hom
        (5 • TrivialCharacterH1.cohomologyClass higher) (Additive.ofMul (Multiplicative.ofAdd 1)) = 5 := by
    rw [map_nsmul]
    change 5 • ((groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (Multiplicative (ZMod 25)) (ZMod 25))).hom
        (TrivialCharacterH1.cohomologyClass higher) (Additive.ofMul (Multiplicative.ofAdd 1))) = 5
    rw [TrivialCharacterH1.class_evaluate]
    decide
  rw [hm, map_zero] at he
  exact (by decide : (5 : ZMod 25) ≠ 0) he
end FreyConnectingPrimeOrderTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInflationCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1Inflation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameClass_inflation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSubmodule
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficient_stable
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientProjection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence_shortExact
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetInvariant
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_ne_zero
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.no_invariant_lift
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetH0
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoset_connecting
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_values_killed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_inertia_class_killed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_tame_class_killed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.residual_exists_connecting_prime_order_H1
