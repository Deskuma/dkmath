/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CurrentSupportObstruction

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower
open DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation
open DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
open IsDedekindDomain
noncomputable section

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

-- All six phases have one ramified factor, including phases outside the selected row.
example (j : Fin 6) :
    phaseCarrierQuotient p (j.val + 1) ∉ SevenCyclotomicDegreeSixInt.ramifiedPrime :=
  phaseCarrierQuotient_not_mem_ramifiedPrime p _ (by have := j.isLt; omega)

-- The ideal-power receiver covers every nontrivial phase, not just 1,4,5.
example (j : Fin 6) : ∃ J : Ideal SevenCyclotomicDegreeSixInt.Ring,
    Ideal.span {phaseCarrierQuotient p (j.val + 1)} = J ^ 7 :=
  normalizedPhaseIdeal_seventh_power h _ (by omega) (by have := j.isLt; omega)

-- Both the obstruction and the repaired global extraction hold for the same carrier.
example (c : CurrentCommonPrimeCyclotomicPacket h q) :
    (¬ ∃ u b : SevenCyclotomicDegreeSixInt.Ring,
      IsUnit u ∧ currentLinearCarrier c = u * b ^ 7) ∧
    (∃ u b : SevenCyclotomicDegreeSixInt.Ring, IsUnit u ∧
      currentLinearCarrier c = SevenCyclotomicDegreeSixInt.ramifiedUniformizer * u * b ^ 7 ∧
      Fermat7Equation x y z) :=
  ⟨currentCarrier_not_unit_mul_seventh_power c, currentCarrier_ramified_element_receiver c⟩

-- No support primes are dropped: the ramified exponent is exactly one and every
-- other exponent is a seventh multiple, even outside the chosen address row.
example (c : CurrentCommonPrimeCyclotomicPacket h q)
    (v : HeightOneSpectrum SevenCyclotomicDegreeSixInt.Ring) :
    (v.asIdeal = SevenCyclotomicDegreeSixInt.ramifiedPrime → exponent (carrierIdeal c) v = 1) ∧
    (v.asIdeal ≠ SevenCyclotomicDegreeSixInt.ramifiedPrime → 7 ∣ exponent (carrierIdeal c) v) := by
  constructor
  · intro hv
    have he : v = ramifiedPlace := by
      apply HeightOneSpectrum.ext
      exact hv
    rw [he]
    exact ramifiedPlace_exponent c
  · exact away_ramified_exponent_seventh_dvd c v

-- The receiver's full-support condition is now proved for the explicit normalized ideal.
example (c : CurrentCommonPrimeCyclotomicPacket h q) :
    normalizedCarrierIdeal c =
      powerRoot (normalizedCarrierIdeal c) (normalizedCarrierIdeal_ne_zero c) 7 ^ 7 :=
  eq_powerRoot_pow _ _ 7 (normalized_completeSupport_seventh_divisibility c)

-- Every new public production definition and theorem is audited.
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.linear_ramified_mem
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.linear_ramified_not_mem_sq
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.gapAxis_dvd
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.gapAxisQuotient
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.gapAxisQuotient_spec
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrier
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrierQuotient
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrier_eq_uniformizer_mul_quotient
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.ramifiedEval_phaseCarrierQuotient
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrierQuotient_not_mem_ramifiedPrime
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrier_mem_ramifiedPrime
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrier_not_mem_ramifiedPrime_sq
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseInverseExponent_not_seven_dvd
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.currentLinearCarrier_eq_phaseCarrier
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.currentLinearCarrier_mem_ramifiedPrime
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.currentLinearCarrier_not_mem_ramifiedPrime_sq
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.six_current_factors_product_direct
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.prime_eq_ramified_of_mem_current_phases
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseIdeals_pairwise
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseProduct_unit_mul_fourteenth_power
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseIdealProduct_seventh_power
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseIdeal_seventh_power
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedCarrierIdeal
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedCarrierIdeal_ne_zero
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedCarrierIdeal_seventh_power
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedCarrier_exponent_seven_dvd
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalized_completeSupport_seventh_divisibility
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramifiedIdeal_mul_seventh_power
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.ramifiedPlace
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.ramifiedPlace_mem_support
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.ramifiedPlace_exponent
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.ramifiedPlace_in_complement
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.away_ramified_exponent_seventh_dvd
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.not_completeSupport_seventh_divisibility
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation.currentCarrier_not_unit_mul_seventh_power

-- Neutral imported endpoints are audited separately from unrelated research stubs.
#print axioms DkMath.FLT.dedekindIdealEqPowOfProdEqPowOfPairwise
#print axioms DkMath.FLT.linearFactorDiffSpanEqSubOneSpan
#print axioms DkMath.FLT.spanSingletons_isCoprime_of_noCommonPrime
