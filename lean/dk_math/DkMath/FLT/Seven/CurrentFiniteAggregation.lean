/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
import DkMath.FLT.Seven.CurrentCarrierCutoff
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID

/-! Aggregation of the current real common-prime rows, and an explicit
complete-support receiver for the current phase-corrected degree-six carrier.
The receiver's exponent hypothesis is not supplied by local membership alone. -/
namespace DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation
open SevenRealCubicInt SevenCyclotomicDegreeSixInt
open IsDedekindDomain
open DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
open scoped NumberField BigOperators
noncomputable section

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

/-- One existing current packet for every prime in the complete rational common support. -/
def commonRow (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : {q : ℕ // q ∈ h.c.primeFactors}) : CurrentCommonPrimeCyclotomicPacket h q.val :=
  Classical.choice (currentCommonPrime_cyclotomicAddress h q.val
    (Nat.prime_of_mem_primeFactors q.property) (Nat.dvd_of_mem_primeFactors q.property))

private theorem quotient_ne_zero (h : DirectOrbitCanonicalCommonFactorPacket p) :
    directOrbitQuotient p ≠ 0 := by
  have hs : h.squareRefinement.quotientSquareRoot ≠ 0 := by
    intro hz
    have hn := directOrbitSquareRefinement_quotient_square_norm_pos h.squareRefinement
    rw [hz] at hn
    norm_num [SevenRealCubicInt.norm] at hn
  obtain ⟨U, hu⟩ := directOrbitQuotient_eq_currentAxis_cube_unit_mul_squareRoot_pow h.squareRefinement
  rw [hu]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 eisensteinAxis_prime.ne_zero)
    U.isUnit.ne_zero) (pow_ne_zero 14 hs)

/-- The actual current real quotient ideal, through the existing model equivalence. -/
def quotientIdeal (_h : DirectOrbitCanonicalCommonFactorPacket p) : Ideal O :=
  currentPrincipalIdeal (directOrbitQuotient p)

theorem quotientIdeal_ne_zero (h : DirectOrbitCanonicalCommonFactorPacket p) :
    quotientIdeal h ≠ 0 := by
  intro hz
  apply quotient_ne_zero h
  apply modelEquivRingOfIntegers.injective
  simpa using (Ideal.span_singleton_eq_bot.mp hz)

/-- The full real quotient ideal already has an axis-cube times seventh-power form. -/
theorem quotientIdeal_axis_cube_seventh_power (h : DirectOrbitCanonicalCommonFactorPacket p) :
    quotientIdeal h = currentPrincipalIdeal eisensteinAxis ^ 3 *
      (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot ^ 2) ^ 7 := by
  obtain ⟨U, hu⟩ := directOrbitQuotient_eq_currentAxis_cube_unit_mul_squareRoot_pow h.squareRefinement
  have hunit : IsUnit (modelEquivRingOfIntegers (U : SevenRealCubicInt)) :=
    U.isUnit.map modelEquivRingOfIntegers.toRingHom
  simp only [quotientIdeal, currentPrincipalIdeal, hu, map_mul, map_pow,
    ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_top.mpr hunit]
  simp only [← Ideal.one_eq_top, mul_one, ← pow_mul]

/-- Exactly the chosen real prime rows, as a subset of the full ideal support.
This does not enumerate every prime above a rational prime. -/
def knownCommonPrime (h : DirectOrbitCanonicalCommonFactorPacket p)
    (v : HeightOneSpectrum O) : Prop :=
  ∃ q : {q : ℕ // q ∈ h.c.primeFactors}, (commonRow h q).residue.Q = v.asIdeal

def commonPowerRoot (h : DirectOrbitCanonicalCommonFactorPacket p) : Ideal O := by
  classical
  exact ∏ v ∈ (support (quotientIdeal h) (quotientIdeal_ne_zero h)).filter (knownCommonPrime h),
    v.asIdeal ^ (exponent (quotientIdeal h) v / 7)

/-- All unselected primes and their exact exponents are retained. -/
def commonRemainder (h : DirectOrbitCanonicalCommonFactorPacket p) : Ideal O := by
  classical
  exact ∏ v ∈ (support (quotientIdeal h) (quotientIdeal_ne_zero h)).filter
    (fun v => ¬ knownCommonPrime h v), v.asIdeal ^ exponent (quotientIdeal h) v

theorem knownCommonPrime_exponent (h : DirectOrbitCanonicalCommonFactorPacket p)
    (v : HeightOneSpectrum O) (hv : knownCommonPrime h v) :
    ∃ e : ℕ, 0 < e ∧ exponent (quotientIdeal h) v = 14 * e := by
  obtain ⟨q, hq⟩ := hv
  let c := commonRow h q
  refine ⟨currentIdealPrimeMultiplicity c.residue.Q
    (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot),
    c.currentQuotientSquareRootMultiplicity_pos, ?_⟩
  simpa only [exponent, quotientIdeal, ← hq, currentIdealPrimeMultiplicity] using
    c.currentQuotientMultiplicity_eq_fourteen_mul (p := p)

/-- The current local rows aggregate over the complete finite ideal support.
The complementary factor is explicit, rather than silently discarded. -/
theorem common_prime_aggregation (h : DirectOrbitCanonicalCommonFactorPacket p) :
    quotientIdeal h = commonPowerRoot h ^ 7 * commonRemainder h := by
  classical
  apply selected_power_factor (quotientIdeal h) (quotientIdeal_ne_zero h) 7 (knownCommonPrime h)
  intro v hv
  obtain ⟨e, _, he⟩ := knownCommonPrime_exponent h v (Finset.mem_filter.mp hv).2
  rw [he]
  omega

variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- The exact current degree-six ideal; its conjugate orientation is fixed by `c`. -/
def carrierIdeal (c : CurrentCommonPrimeCyclotomicPacket h q) :
    Ideal SevenCyclotomicDegreeSixInt.Ring := Ideal.span {currentLinearCarrier c}

theorem carrierIdeal_ne_zero (c : CurrentCommonPrimeCyclotomicPacket h q) :
    carrierIdeal c ≠ 0 := by
  intro hz
  have hzero := Ideal.span_singleton_eq_bot.mp hz
  apply c.currentLinearCarrier_not_mem_conjugateKernel
  rw [hzero]
  exact Ideal.zero_mem _

/-- Every current degree-six prime and its exact exponent is included, even
when no current common-prime row has yet identified its orientation. -/
theorem carrier_full_factorization (c : CurrentCommonPrimeCyclotomicPacket h q) :
    carrierIdeal c = ∏ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
      v.asIdeal ^ exponent (carrierIdeal c) v := factorization _ _

/-- Current local membership and exclusion retain the conjugate orientation. -/
theorem current_orientation (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∈ c.address.currentKernel ∧
    currentLinearCarrier c ∉ c.address.conjugate.currentKernel ∧
    currentConjugateLinearCarrier c ∈ c.address.conjugate.currentKernel ∧
    currentConjugateLinearCarrier c ∉ c.address.currentKernel :=
  ⟨c.currentLinearCarrier_mem_currentKernel, c.currentLinearCarrier_not_mem_conjugateKernel,
    c.currentConjugateLinearCarrier_mem_conjugateKernel,
    c.currentConjugateLinearCarrier_not_mem_currentKernel⟩

/-- The oriented current row gives an exact exponent in the complete carrier support. -/
theorem carrier_local_exponent (c : CurrentCommonPrimeCyclotomicPacket h q)
    (v : HeightOneSpectrum SevenCyclotomicDegreeSixInt.Ring)
    (hv : v.asIdeal = c.address.currentKernel) :
    exponent (carrierIdeal c) v = 14 * currentIdealPrimeMultiplicity c.residue.Q
      (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
  apply principal_exponent_eq _ v (carrierIdeal_ne_zero c)
  · rw [hv]
    exact c.currentLinearCarrier_mem_power
  · rw [hv]
    exact c.currentLinearCarrier_not_mem_power_succ

/-- The identified current row contributes a seventh power; every other
current degree-six prime is kept with its exact exponent. -/
theorem carrier_local_aggregation (c : CurrentCommonPrimeCyclotomicPacket h q) :
    carrierIdeal c =
      (∏ v ∈ (support (carrierIdeal c) (carrierIdeal_ne_zero c)).filter
        (fun v => v.asIdeal = c.address.currentKernel),
        v.asIdeal ^ (exponent (carrierIdeal c) v / 7)) ^ 7 *
      ∏ v ∈ (support (carrierIdeal c) (carrierIdeal_ne_zero c)).filter
        (fun v => v.asIdeal ≠ c.address.currentKernel),
        v.asIdeal ^ exponent (carrierIdeal c) v := by
  classical
  apply selected_power_factor
  intro v hv
  rw [carrier_local_exponent c v (Finset.mem_filter.mp hv).2]
  omega

/-- Complete-support receiver: every exponent condition is an explicit hypothesis. -/
theorem carrier_ideal_seventh_power (c : CurrentCommonPrimeCyclotomicPacket h q)
    (hdiv : ∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
      7 ∣ exponent (carrierIdeal c) v) :
    carrierIdeal c = powerRoot (carrierIdeal c) (carrierIdeal_ne_zero c) 7 ^ 7 :=
  eq_powerRoot_pow _ _ 7 hdiv

/-- The current carrier is a unit times an actual seventh power only after
all current support exponents have been supplied. The unit and original
Fermat equation are retained; no smaller successor is asserted. -/
theorem carrier_element_receiver (c : CurrentCommonPrimeCyclotomicPacket h q)
    (hdiv : ∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
      7 ∣ exponent (carrierIdeal c) v) :
    ∃ u beta : SevenCyclotomicDegreeSixInt.Ring, IsUnit u ∧
      currentLinearCarrier c = u * beta ^ 7 ∧ Fermat7Equation x y z := by
  obtain ⟨u, hu, hpow⟩ := unitMulPowOfSpanEqPow (carrier_ideal_seventh_power c hdiv)
  exact ⟨u, _, hu, hpow, source.hEq⟩

end
end DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation
