/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID
import DkMath.FLT.Seven.SevenRamifiedFusionSeventhPowerResidualIdealExtraction

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionElementLevelOrientedPower"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace SevenCyclotomicDegreeSixInt

/-- Element-level extraction from a principal-ideal identity with one
distinguished factor and one power factor.

The unit supplied by equality of principal ideals is absorbed into the
distinguished factor.  In particular, this statement does not require the
unit to be an `n`-th power. -/
theorem exists_mul_pow_of_span_eq_mul_pow
    {a : Ring} {L R : Ideal Ring} {n : ℕ}
    (h : Ideal.span {a} = L * R ^ n) :
    ∃ l r : Ring,
      Ideal.span {l} = L ∧
      Ideal.span {r} = R ∧
      a = l * r ^ n := by
  let l₀ : Ring := Submodule.IsPrincipal.generator L
  let r : Ring := Submodule.IsPrincipal.generator R
  have hl₀ : Ideal.span {l₀} = L := by
    exact Ideal.span_singleton_generator L
  have hr : Ideal.span {r} = R := by
    exact Ideal.span_singleton_generator R
  have hprincipal :
      Ideal.span {a} = Ideal.span {l₀ * r ^ n} := by
    calc
      Ideal.span {a} = L * R ^ n := h
      _ = Ideal.span {l₀} * Ideal.span {r} ^ n := by
        rw [hl₀, hr]
      _ = Ideal.span {l₀ * r ^ n} := by
        rw [Ideal.span_singleton_pow,
          Ideal.span_singleton_mul_span_singleton]
  have hassociated :
      Associated a (l₀ * r ^ n) :=
    Ideal.span_singleton_eq_span_singleton.mp hprincipal
  rcases hassociated with ⟨u, hu⟩
  refine
    ⟨↑(u⁻¹) * l₀, r, ?_, hr, ?_⟩
  · calc
      Ideal.span {↑(u⁻¹) * l₀} =
          Ideal.span {l₀} := by
        exact
          Ideal.span_singleton_mul_left_unit
            (u⁻¹).isUnit l₀
      _ = L := hl₀
  · calc
      a = a * ↑u * ↑(u⁻¹) := by
        simp [mul_assoc]
      _ = (l₀ * r ^ n) * ↑(u⁻¹) := by
        rw [hu]
      _ = (↑(u⁻¹) * l₀) * r ^ n := by
        ring

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootRoutingPacket

open SevenCyclotomicDegreeSixInt

namespace QuotientPrimeSupport

variable {p : RamifiedSignedRootRoutingPacket}

/-- Exact oriented element-level seventh-power witness.

The load element includes the unique ramified factor, all prescribed routed
load factors, and the associated unit coming from principal-ideal equality.
The residual root contains exactly the oriented residual ideal. -/
structure OrientedElementLevelPowerWitness
    (p : RamifiedSignedRootRoutingPacket) where
  loadElement : SevenCyclotomicDegreeSixInt.Ring
  residualRoot : SevenCyclotomicDegreeSixInt.Ring
  span_loadElement :
    Ideal.span {loadElement} =
      globalOrientedLoadedCarrierIdeal (p := p)
  span_residualRoot :
    Ideal.span {residualRoot} =
      globalOrientedResidualIdeal (p := p)
  carrier_eq :
    p.signedDepth.cyclotomicDegreeSixCarrier =
      loadElement * residualRoot ^ 7

/-- The concrete PID produces an exact oriented element-level witness. -/
theorem exists_orientedElementLevelPowerWitness
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (OrientedElementLevelPowerWitness p) := by
  rcases
      SevenCyclotomicDegreeSixInt.exists_mul_pow_of_span_eq_mul_pow
        (span_carrier_eq_loadedCarrier_mul_residual_pow (p := p)) with
    ⟨l, r, hl, hr, hcarrier⟩
  exact
    ⟨⟨l, r, hl, hr, hcarrier⟩⟩

/-- Canonical (choice-based) oriented U1.4 witness. -/
def orientedElementLevelPowerWitness
    (p : RamifiedSignedRootRoutingPacket) :
    OrientedElementLevelPowerWitness p :=
  Classical.choice (exists_orientedElementLevelPowerWitness p)

/-- The oriented load element, with the associated unit absorbed. -/
def orientedLoadElement
    (p : RamifiedSignedRootRoutingPacket) :
    SevenCyclotomicDegreeSixInt.Ring :=
  (orientedElementLevelPowerWitness p).loadElement

/-- The oriented residual seventh root. -/
def orientedResidualRoot
    (p : RamifiedSignedRootRoutingPacket) :
    SevenCyclotomicDegreeSixInt.Ring :=
  (orientedElementLevelPowerWitness p).residualRoot

theorem span_orientedLoadElement
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {orientedLoadElement p} =
      globalOrientedLoadedCarrierIdeal (p := p) :=
  (orientedElementLevelPowerWitness p).span_loadElement

/-- Expanded principal-ideal specification of the oriented load element. -/
theorem span_orientedLoadElement_eq_ramified_mul_loadedHalfIdeal
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {orientedLoadElement p} =
      SevenCyclotomicDegreeSixInt.ramifiedPrime *
        globalOrientedLoadedHalfIdeal (p := p) := by
  rw [span_orientedLoadElement,
    globalOrientedLoadedCarrierIdeal]

theorem span_orientedResidualRoot
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {orientedResidualRoot p} =
      globalOrientedResidualIdeal (p := p) :=
  (orientedElementLevelPowerWitness p).span_residualRoot

/-- Exact oriented carrier equation.  No separate unit remains. -/
theorem cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow
    (p : RamifiedSignedRootRoutingPacket) :
    p.signedDepth.cyclotomicDegreeSixCarrier =
      orientedLoadElement p * orientedResidualRoot p ^ 7 :=
  (orientedElementLevelPowerWitness p).carrier_eq

/-- The conjugate load element chosen coherently by quadratic star. -/
def conjugateLoadElement
    (p : RamifiedSignedRootRoutingPacket) :
    SevenCyclotomicDegreeSixInt.Ring :=
  star (orientedLoadElement p)

/-- The conjugate residual root chosen coherently by quadratic star. -/
def conjugateResidualRoot
    (p : RamifiedSignedRootRoutingPacket) :
    SevenCyclotomicDegreeSixInt.Ring :=
  star (orientedResidualRoot p)

theorem span_conjugateLoadElement
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {conjugateLoadElement p} =
      globalConjugateLoadedCarrierIdeal (p := p) := by
  have hmap :=
    congrArg
      (Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
      (span_orientedLoadElement p)
  simpa only [conjugateLoadElement, Ideal.map_span,
    Set.image_singleton,
    map_star_globalOrientedLoadedCarrierIdeal] using hmap

/-- Expanded principal-ideal specification of the conjugate load element. -/
theorem span_conjugateLoadElement_eq_ramified_mul_loadedHalfIdeal
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {conjugateLoadElement p} =
      SevenCyclotomicDegreeSixInt.ramifiedPrime *
        globalConjugateLoadedHalfIdeal (p := p) := by
  rw [span_conjugateLoadElement,
    globalConjugateLoadedCarrierIdeal]

theorem span_conjugateResidualRoot
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {conjugateResidualRoot p} =
      globalConjugateResidualIdeal (p := p) := by
  have hmap :=
    congrArg
      (Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
      (span_orientedResidualRoot p)
  simpa only [conjugateResidualRoot, Ideal.map_span,
    Set.image_singleton,
    map_star_globalOrientedResidualIdeal] using hmap

/-- Exact conjugate carrier equation obtained from the oriented equation by
quadratic conjugation. -/
theorem cyclotomicDegreeSixCarrierConj_eq_load_mul_residualRoot_pow
    (p : RamifiedSignedRootRoutingPacket) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj =
      conjugateLoadElement p * conjugateResidualRoot p ^ 7 := by
  have hstar :=
    congrArg star
      (cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow p)
  calc
    p.signedDepth.cyclotomicDegreeSixCarrierConj =
        star (orientedResidualRoot p) ^ 7 *
          star (orientedLoadElement p) := by
      simpa only
        [RamifiedSignedRootDepthPacket.star_cyclotomicDegreeSixCarrier,
          star_mul, star_pow] using hstar
    _ =
        conjugateLoadElement p *
          conjugateResidualRoot p ^ 7 := by
      rw [conjugateLoadElement, conjugateResidualRoot, mul_comm]

/-- Exact conjugate element-level seventh-power witness, constructed from
the oriented choice rather than by a second independent generator choice. -/
structure ConjugateElementLevelPowerWitness
    (p : RamifiedSignedRootRoutingPacket) where
  loadElement : SevenCyclotomicDegreeSixInt.Ring
  residualRoot : SevenCyclotomicDegreeSixInt.Ring
  span_loadElement :
    Ideal.span {loadElement} =
      globalConjugateLoadedCarrierIdeal (p := p)
  span_residualRoot :
    Ideal.span {residualRoot} =
      globalConjugateResidualIdeal (p := p)
  carrier_eq :
    p.signedDepth.cyclotomicDegreeSixCarrierConj =
      loadElement * residualRoot ^ 7

/-- Canonical conjugate witness, definitionally compatible with the oriented
witness under quadratic star. -/
def conjugateElementLevelPowerWitness
    (p : RamifiedSignedRootRoutingPacket) :
    ConjugateElementLevelPowerWitness p :=
  ⟨conjugateLoadElement p, conjugateResidualRoot p,
    span_conjugateLoadElement p,
    span_conjugateResidualRoot p,
    cyclotomicDegreeSixCarrierConj_eq_load_mul_residualRoot_pow p⟩

/-- The star-compatible conjugate witness exists. -/
theorem exists_conjugateElementLevelPowerWitness
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (ConjugateElementLevelPowerWitness p) :=
  ⟨conjugateElementLevelPowerWitness p⟩

/-- Compact U1.4 element-level extraction packet. -/
theorem elementLevelOrientedPowerPacket
    (p : RamifiedSignedRootRoutingPacket) :
    ∃ loadElement residualRoot :
        SevenCyclotomicDegreeSixInt.Ring,
      Ideal.span {loadElement} =
          SevenCyclotomicDegreeSixInt.ramifiedPrime *
            globalOrientedLoadedHalfIdeal (p := p) ∧
      Ideal.span {residualRoot} =
          globalOrientedResidualIdeal (p := p) ∧
      p.signedDepth.cyclotomicDegreeSixCarrier =
        loadElement * residualRoot ^ 7 := by
  exact
    ⟨orientedLoadElement p, orientedResidualRoot p,
      span_orientedLoadElement_eq_ramified_mul_loadedHalfIdeal p,
      span_orientedResidualRoot p,
      cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow p⟩

/-- Both carrier equations and their literal star compatibility. -/
theorem elementLevelOrientedConjugatePowerPacket
    (p : RamifiedSignedRootRoutingPacket) :
    p.signedDepth.cyclotomicDegreeSixCarrier =
        orientedLoadElement p * orientedResidualRoot p ^ 7 ∧
      p.signedDepth.cyclotomicDegreeSixCarrierConj =
        conjugateLoadElement p * conjugateResidualRoot p ^ 7 ∧
      conjugateLoadElement p = star (orientedLoadElement p) ∧
      conjugateResidualRoot p = star (orientedResidualRoot p) ∧
      Ideal.span {orientedLoadElement p} =
        globalOrientedLoadedCarrierIdeal (p := p) ∧
      Ideal.span {conjugateLoadElement p} =
        globalConjugateLoadedCarrierIdeal (p := p) ∧
      Ideal.span {orientedResidualRoot p} =
        globalOrientedResidualIdeal (p := p) ∧
      Ideal.span {conjugateResidualRoot p} =
        globalConjugateResidualIdeal (p := p) :=
  ⟨cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow p,
    cyclotomicDegreeSixCarrierConj_eq_load_mul_residualRoot_pow p,
    rfl, rfl,
    span_orientedLoadElement p,
    span_conjugateLoadElement p,
    span_orientedResidualRoot p,
    span_conjugateResidualRoot p⟩

end QuotientPrimeSupport

end RamifiedSignedRootRoutingPacket

#print axioms
  SevenCyclotomicDegreeSixInt.exists_mul_pow_of_span_eq_mul_pow
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.cyclotomicDegreeSixCarrierConj_eq_load_mul_residualRoot_pow
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.elementLevelOrientedPowerPacket
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.elementLevelOrientedConjugatePowerPacket

end

end DkMath.FLT.Seven
