/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealGNConservation

#print "file: DkMathTest.FLT.Kummer.SevenRealGNConservation"

namespace DkMathTest.FLT.Kummer.SevenRealGNConservation

open DkMath.FLT.Seven DkMath.Lib.Algebra DkMath.FLT.Kummer.SevenRealGN

-- The phase component takes values in an actual seven-element group.
example : Nat.card (rootsOfUnity 7 C) = 7 := phase_target_card

-- A real-primary unit can have a nonzero norm obstruction, with no hypothetical FLT solution.
example : RealPrimary alphaEmbeddedUnit SevenRealCubicInt.alpha ∧
    normCoordinates alphaEmbeddedUnit = (3, 3) ∧ phaseCharacter alphaEmbeddedUnit = 1 ∧
    ¬ ∃ k : Cˣ, alphaEmbeddedUnit = k ^ 7 :=
  ⟨alphaEmbeddedUnit_primary, alphaEmbeddedUnit_normCoordinates,
    realPrimary_phase_eq_one _ _ alphaEmbeddedUnit_primary, alphaEmbeddedUnit_not_seventh⟩

private theorem zeta_norm_zero : normCoordinates SevenCyclotomicDegreeSixInt.zetaUnit = 0 := by
  have hn : Units.map DkMath.FLT.Kummer.SevenPrimaryNorm.relativeNorm
      SevenCyclotomicDegreeSixInt.zetaUnit = 1 := by
    apply Units.ext
    change QuadraticAlgebra.norm SevenCyclotomicDegreeSixInt.zeta = 1
    simp [QuadraticAlgebra.norm_def, SevenCyclotomicDegreeSixInt.zeta]
  unfold normCoordinates
  rw [hn]
  simp

private theorem zeta_ratio : unitRatio SevenCyclotomicDegreeSixInt.zetaUnit =
    SevenCyclotomicDegreeSixInt.zetaUnit ^ 2 := by
  have hc : unitConj SevenCyclotomicDegreeSixInt.zetaUnit =
      SevenCyclotomicDegreeSixInt.zetaUnit⁻¹ := by
    apply Units.ext
    change star SevenCyclotomicDegreeSixInt.zeta = SevenCyclotomicDegreeSixInt.zetaInv
    apply QuadraticAlgebra.ext <;>
      simp [SevenCyclotomicDegreeSixInt.zeta, SevenCyclotomicDegreeSixInt.zetaInv]
  change SevenCyclotomicDegreeSixInt.zetaUnit * (unitConj SevenCyclotomicDegreeSixInt.zetaUnit)⁻¹ = _
  rw [hc, inv_inv, pow_two]

-- The other direction is essential too: norm zero alone does not kill the phase.
example : normCoordinates SevenCyclotomicDegreeSixInt.zetaUnit = 0 ∧
    phaseCharacter SevenCyclotomicDegreeSixInt.zetaUnit ≠ 1 := by
  refine ⟨zeta_norm_zero, ?_⟩
  intro hp
  have hh : unitRatio SevenCyclotomicDegreeSixInt.zetaUnit ^ 8 = 1 := congrArg Subtype.val hp
  rw [zeta_ratio, ← pow_mul] at hh
  have hz : SevenCyclotomicDegreeSixInt.zetaUnit ^ 16 =
      SevenCyclotomicDegreeSixInt.zetaUnit ^ 2 := by
    rw [show 16 = 7 * 2 + 2 by decide, pow_add, pow_mul,
      SevenCyclotomicDegreeSixInt.zetaUnit_pow_seven, one_pow, one_mul]
  rw [hz] at hh
  have hv : SevenCyclotomicDegreeSixInt.zeta ^ 2 = 1 := congrArg Units.val hh
  have hd := SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot.dvd_of_pow_eq_one 2 hv
  norm_num at hd

-- Equality of all three coordinates recognizes the actual unit seventh-power class.
example (u v : Cˣ) (h : unitObstruction u = unitObstruction v) :
    (u : Cˣ ⧸ unitPowerSubgroup C 7) = (v : Cˣ ⧸ unitPowerSubgroup C 7) :=
  sameUnitPowerClass_iff_quotient_eq.mp ((same_class_iff_unitObstruction_eq u v).mpr h)

-- This noninteger real-primary example has an actual nonzero source and root away from lambda.
private noncomputable def P : PrimaryPacket := packetOfRealUnit SevenRealCubicInt.alphaUnit

example : P.source ≠ 0 ∧ normCoordinates P.delta = (3, 3) :=
  ⟨P.source_ne_zero, alphaEmbeddedUnit_normCoordinates⟩

-- An allowed gauge really changes the root, while preserving the original source and primary condition.
example : (regauge P zetaGauge).gamma = SevenCyclotomicDegreeSixInt.zeta ∧
    (regauge P zetaGauge).gamma ≠ P.gamma ∧
    (regauge P zetaGauge).source = P.source ∧
    RealPrimary (regauge P zetaGauge).delta (-P.parameter) := by
  refine ⟨by change SevenCyclotomicDegreeSixInt.zeta * 1 = _; exact mul_one _, ?_,
    (source_preservation P zetaGauge).1, (coefficient_ring_preservation P zetaGauge).2.2.2⟩
  change SevenCyclotomicDegreeSixInt.zeta * 1 ≠ 1
  simpa only [mul_one] using SevenCyclotomicDegreeSixInt.zeta_ne_one

-- No sequence of such root changes can remove the real norm obstruction.
example (ts : List AllowedGauge) : normCoordinates (iterate P ts).delta = (3, 3) ∧
    ¬ ∃ k : Cˣ, (iterate P ts).delta = k ^ 7 := by
  have ho := congrArg ConservedData.obstruction (iterated_invariant_preservation P ts).1
  have hn : normCoordinates (iterate P ts).delta = normCoordinates P.delta := congrArg Prod.fst ho
  change normCoordinates (iterate P ts).delta = normCoordinates alphaEmbeddedUnit at hn
  rw [alphaEmbeddedUnit_normCoordinates] at hn
  refine ⟨hn, ?_⟩
  intro hk
  have hz := (unit_seventh_iff_obstruction _).mp hk
  rw [hn] at hz
  exact (by decide : (3 : ZMod 7) ≠ 0) (congrArg Prod.fst hz.1)

-- The iteration carries actual packet proofs; the ideal-based measure never decreases.
example (ts : List AllowedGauge) (m : Ideal C → ℕ) :
    RealPrimary (iterate P ts).delta (-P.parameter) ∧
    ¬ SevenCyclotomicDegreeSixInt.ramifiedUniformizer ∣ (iterate P ts).gamma ∧
    ¬ m (Ideal.span ({(iterate P ts).gamma} : Set C)) < m (Ideal.span ({P.gamma} : Set C)) :=
  ⟨(iterated_invariant_preservation P ts).2.1, (iterated_invariant_preservation P ts).2.2,
    no_ideal_measure_drop P ts m⟩

-- Going forward and back really restores both the root and the unit.
example (Q : PrimaryPacket) (t : AllowedGauge) :
    (regauge (regauge Q t) (inverseGauge t)).gamma = Q.gamma ∧
    (regauge (regauge Q t) (inverseGauge t)).delta = Q.delta := by
  constructor
  · change (↑t.val⁻¹ : C) * ((t.val : C) * Q.gamma) = Q.gamma
    have hc : (↑t.val⁻¹ : C) * (t.val : C) = 1 := t.val.inv_val
    rw [← mul_assoc, hc, one_mul]
  · change (Q.delta * t.val⁻¹ ^ 7) * (t.val⁻¹)⁻¹ ^ 7 = Q.delta
    rw [inv_inv, mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]

end DkMathTest.FLT.Kummer.SevenRealGNConservation
