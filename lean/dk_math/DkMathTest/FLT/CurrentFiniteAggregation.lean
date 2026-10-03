/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CurrentFiniteAggregation

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentAggregation
open DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
open IsDedekindDomain
open scoped BigOperators
noncomputable section

-- Empty selections retain the entire ideal, rather than silently proving a power.
example {R : Type*} [CommRing R] [IsDedekindDomain R] (I : Ideal R) (hi : I ≠ 0) :
    I = ∏ v ∈ support I hi, v.asIdeal ^ exponent I v := by
  have hp := selected_power_factor I hi 7 (fun _ => False) (by simp)
  simpa only [Finset.filter_false, Finset.prod_empty, one_pow, one_mul, not_false_eq_true, Finset.filter_true] using hp

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable (h : DirectOrbitCanonicalCommonFactorPacket p)

-- The degenerate common support gives root one, while retaining the full remainder.
example (hc : h.c = 1) : commonPowerRoot h = 1 := by
  classical
  have hn : ∀ v, ¬ knownCommonPrime h v := by
    intro v hv
    obtain ⟨q, _⟩ := hv
    have hq := q.property
    simp [hc] at hq
  simp [commonPowerRoot, hn]

example (hc : h.c = 1) : commonRemainder h = quotientIdeal h := by
  have hr : commonPowerRoot h = 1 := by
    classical
    have hn : ∀ v, ¬ knownCommonPrime h v := by
      intro v hv
      obtain ⟨q, _⟩ := hv
      have hq := q.property
      simp [hc] at hq
    simp [commonPowerRoot, hn]
  simpa only [hr, one_pow, one_mul] using (common_prime_aggregation h).symm

-- Every rational common prime gets a current packet, with the correct orientation
-- and exact exponent; no scalar-norm equality is used as a carrier identity.
example (q : {q : ℕ // q ∈ h.c.primeFactors}) (k : ℕ) :
    currentLinearCarrier (commonRow h q) ∈ (commonRow h q).address.currentKernel ^ k ↔
      k ≤ 14 * currentIdealPrimeMultiplicity (commonRow h q).residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) :=
  (commonRow h q).currentLinearCarrier_mem_power_iff k

-- The receiver exposes the complete-support obligation and retains the source equation.
example {q : ℕ} (c : CurrentCommonPrimeCyclotomicPacket h q)
    (hd : ∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
      7 ∣ exponent (carrierIdeal c) v) :
    ∃ u b : SevenCyclotomicDegreeSixInt.Ring, IsUnit u ∧
      currentLinearCarrier c = u * b ^ 7 ∧ Fermat7Equation x y z :=
  carrier_element_receiver c hd

#print axioms mem_support
#print axioms DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation.factorization
#print axioms eq_powerRoot_pow
#print axioms partition
#print axioms selected_power_factor
#print axioms CurrentMuSevenResidueAddress.currentLocalEval_conjugate_star
#print axioms CurrentMuSevenResidueAddress.map_star_currentKernel
#print axioms CurrentCommonPrimeCyclotomicPacket.current_star_mem_conjugate_power
#print axioms CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_mem_power
#print axioms CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_not_mem_power_succ
#print axioms CurrentCommonPrimeCyclotomicPacket.currentLinearCarrier_mem_power_iff
#print axioms quotientIdeal_ne_zero
#print axioms quotientIdeal_axis_cube_seventh_power
#print axioms knownCommonPrime_exponent
#print axioms common_prime_aggregation
#print axioms carrierIdeal_ne_zero
#print axioms carrier_full_factorization
#print axioms current_orientation
#print axioms carrier_ideal_seventh_power
#print axioms carrier_element_receiver

#print axioms principal_exponent_eq
#print axioms carrier_local_exponent
#print axioms carrier_local_aggregation
