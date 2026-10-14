/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CurrentCarrierNormalizedPower

/-! The ramified prime is an actual member of the complete support of the raw
current carrier. Its exponent one obstructs unnormalized seventh-power extraction.
All statements retain the current counterexample/provenance hypotheses. -/
namespace DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation
open SevenRealCubicInt SevenCyclotomicDegreeSixInt
open IsDedekindDomain
open CurrentCarrierRamification
open DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
noncomputable section

private theorem ramifiedPrime_ne_bot : ramifiedPrime ≠ (⊥ : Ideal Ring) := by
  intro hz
  have hm : ramifiedUniformizer ∈ ramifiedPrime := ramifiedEval_uniformizer
  rw [hz] at hm
  exact ramifiedUniformizer_ne_zero (Ideal.mem_bot.mp hm)

/-- The actual nonzero height-one prime above seven in the current degree-six ring. -/
def ramifiedPlace : HeightOneSpectrum Ring :=
  ⟨ramifiedPrime, ramifiedPrime_isMaximal.isPrime, ramifiedPrime_ne_bot⟩

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- The ramified prime occurs in the raw current carrier's complete support. -/
theorem ramifiedPlace_mem_support (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ramifiedPlace ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c) := by
  apply (mem_support _ _ _).mpr
  apply Ideal.dvd_iff_le.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact currentLinearCarrier_mem_ramifiedPrime c

/-- Its exponent is one, not a seventh multiple. -/
theorem ramifiedPlace_exponent (c : CurrentCommonPrimeCyclotomicPacket h q) :
    exponent (carrierIdeal c) ramifiedPlace = 1 := by
  apply principal_exponent_eq _ _ (carrierIdeal_ne_zero c) 1
  · change currentLinearCarrier c ∈ ramifiedPrime ^ 1
    simpa only [pow_one] using currentLinearCarrier_mem_ramifiedPrime c
  · change currentLinearCarrier c ∉ ramifiedPrime ^ 2
    exact currentLinearCarrier_not_mem_ramifiedPrime_sq c

/-- The obstruction lies in the explicit complement of the selected current row,
and is distinct from that row's conjugate too. -/
theorem ramifiedPlace_in_complement (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ramifiedPlace ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c) ∧
      ramifiedPlace.asIdeal ≠ c.address.currentKernel ∧
      ramifiedPlace.asIdeal ≠ c.address.conjugate.currentKernel ∧
      exponent (carrierIdeal c) ramifiedPlace = 1 := by
  refine ⟨ramifiedPlace_mem_support c, ?_, ?_, ramifiedPlace_exponent c⟩
  · intro he
    have hm := carrier_local_exponent c ramifiedPlace he
    rw [ramifiedPlace_exponent c] at hm
    omega
  · intro he
    have hm := currentLinearCarrier_mem_ramifiedPrime c
    change currentLinearCarrier c ∈ ramifiedPlace.asIdeal at hm
    rw [he] at hm
    exact c.currentLinearCarrier_not_mem_conjugateKernel hm

/-- Every prime other than the actual ramified prime has a seventh-multiple
exponent. This controls the entire complementary support without an address list. -/
theorem away_ramified_exponent_seventh_dvd
    (c : CurrentCommonPrimeCyclotomicPacket h q) (v : HeightOneSpectrum Ring)
    (hv : v.asIdeal ≠ ramifiedPrime) : 7 ∣ exponent (carrierIdeal c) v := by
  obtain ⟨J, he⟩ := CurrentCarrierPower.currentCarrier_ramifiedIdeal_mul_seventh_power c
  have hj : J ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : 7 ≠ 0), mul_zero] at he
    exact carrierIdeal_ne_zero c he
  have hp0 : exponent ramifiedPrime v = 0 := by
    by_contra hn
    have hd : v.asIdeal ∣ ramifiedPrime :=
      (Associates.count_ne_zero_iff_dvd ramifiedPrime_ne_bot v.irreducible).mp hn
    have hle := Ideal.le_of_dvd hd
    exact hv (ramifiedPrime_isMaximal.eq_of_le v.isPrime.ne_top hle).symm
  have hi : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  have hp := Associates.mk_ne_zero.mpr ramifiedPrime_ne_bot
  have hj' := Associates.mk_ne_zero.mpr hj
  unfold exponent
  rw [he, ← Associates.mk_mul_mk, Associates.mk_pow,
    Associates.count_mul hp (pow_ne_zero 7 hj') hi, Associates.count_pow hj' hi]
  change 7 ∣ exponent ramifiedPrime v + 7 * exponent J v
  rw [hp0, zero_add]
  exact dvd_mul_right 7 _

/-- The DRC-008 complete-support hypothesis is false for the raw current carrier.
This conditional structural statement does not assert existence of an FLT counterexample. -/
theorem not_completeSupport_seventh_divisibility
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ¬ (∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
      7 ∣ exponent (carrierIdeal c) v) := by
  intro hd
  have hn := hd ramifiedPlace (ramifiedPlace_mem_support c)
  rw [ramifiedPlace_exponent c] at hn
  norm_num at hn

/-- A unit cannot remove the ramified exponent-one obstruction. -/
theorem currentCarrier_not_unit_mul_seventh_power
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ¬ ∃ u b : Ring, IsUnit u ∧ currentLinearCarrier c = u * b ^ 7 := by
  rintro ⟨u, b, hu, he⟩
  let hp : ramifiedPrime.IsPrime := ramifiedPrime_isMaximal.isPrime
  have hm := currentLinearCarrier_mem_ramifiedPrime c
  rw [he] at hm
  have hbpow : b ^ 7 ∈ ramifiedPrime := (hp.mem_or_mem hm).resolve_left (fun h =>
    hp.ne_top (ramifiedPrime.eq_top_of_isUnit_mem h hu))
  have hb : b ∈ ramifiedPrime := hp.mem_of_pow_mem 7 hbpow
  have hb7 : b ^ 7 ∈ ramifiedPrime ^ 7 := Ideal.pow_mem_pow hb 7
  have hb2 : b ^ 7 ∈ ramifiedPrime ^ 2 := Ideal.pow_le_pow_right (by decide : 2 ≤ 7) hb7
  apply currentLinearCarrier_not_mem_ramifiedPrime_sq c
  rw [he]
  exact (ramifiedPrime ^ 2).mul_mem_left u hb2

end
end DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation
