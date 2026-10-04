/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate
import DkMathTest.NumberTheory.LegendreIncidenceUpper

#print "file: DkMathTest.NumberTheory.LegendreHybridProvider"

namespace DkMathTest.LegendreHybridProvider

open DkMath.NumberTheory.Legendre
open DkMathTest.LegendreIncidenceUpper DkMathTest.LegendreBlockLocalization
open scoped BigOperators

theorem twoPrimeUpper_eq_finite (n : ℕ) :
    paritySafeTwoPrimeIncidenceUpper n =
      ∑ q ∈ (Finset.range (n + 1)).filter (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2),
        paritySafeTwoPrimeWaveUpper n q := by
  rw [paritySafeTwoPrimeIncidenceUpper, oddActive_eq_filter_range]

set_option maxRecDepth 20000 in
theorem mainBlock_pair_upper :
    (∑ i ∈ Finset.range 20, paritySafeTwoPrimeIncidenceUpper (20 + i + 1)) = 418 := by
  simp_rw [twoPrimeUpper_eq_finite]
  decide +kernel

theorem mainBlock_pair_upper_strict_gain :
    (∑ i ∈ Finset.range 20, paritySafeTwoPrimeIncidenceUpper (20 + i + 1)) <
      (∑ i ∈ Finset.range 20, paritySafeIncidenceUpper (20 + i + 1)) := by
  rw [mainBlock_pair_upper, mainBlock_structural_upper]
  decide

theorem shell21_pair_upper_strict_gain :
    paritySafeTwoPrimeIncidenceUpper 21 = 6 ∧
      paritySafeTwoPrimeIncidenceUpper 21 < paritySafeIncidenceUpper 21 := by
  rw [twoPrimeUpper_eq_finite, shell21_cap_and_candidate.1]
  decide +kernel

set_option maxRecDepth 20000 in
theorem six_residual_waves_pair_corrected :
    ∀ t ∈ residualWaveCalibration,
      paritySafeTwoPrimeWaveUpper t.1 t.2.1 = t.2.2.2 := by
  decide +kernel

theorem six_residual_waves_pair_exact_diagnostic :
    ∀ t ∈ residualWaveCalibration,
      paritySafeTwoPrimeWaveUpper t.1 t.2.1 = (paritySafeActiveWaveOffsets t.1 t.2.1).card := by
  intro t ht
  rw [six_residual_waves_pair_corrected t ht, (residual_wave_slack_calibration t ht).2]

/-- An incomplete anchor exclusion is not in general an exact wave count. -/
theorem incomplete_pair_exclusion_not_exact :
    paritySafePairDivisorWaveUpper 105 19 3 5 = 4 ∧
      (paritySafeActiveWaveOffsets 105 19).card = 3 := by
  rw [activeWave_eq_finite]
  decide +kernel

/-- Subtracting both divisor counts without intersection credit can undershoot the actual wave. -/
theorem missing_intersection_credit_not_upper :
    paritySafeOddQuotientUpper 30 7 -
      (paritySafeOddMultipleFloorDelta (30 ^ 2 / 7) ((30 ^ 2 + 2 * 30) / 7) 3 +
        paritySafeOddMultipleFloorDelta (30 ^ 2 / 7) ((30 ^ 2 + 2 * 30) / 7) 5) = 2 ∧
      paritySafePairDivisorWaveUpper 30 7 3 5 = 3 ∧
      (paritySafeActiveWaveOffsets 30 7).card = 3 := by
  rw [activeWave_eq_finite]
  decide +kernel

/-- Exact point identities accompany the local support witnesses, without global excess evaluation. -/
theorem shell29_point_factorizations :
    29 ^ 2 + 14 = 3 ^ 2 * 5 * 19 ∧ 29 ^ 2 + 56 = 3 * 13 * 23 := by
  decide

theorem shell29_candidate_seats :
    (14 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 29 ∧
      (56 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 29 := by
  rw [candidate_eq_filter_Icc]
  decide

/-- Membership unfolds exactly the prime, bound, anchor exclusion and point divisibility conditions. -/
theorem shell29_support_witnesses :
    ({3, 5, 19} : Finset ℕ) ⊆ paritySafeActiveSupport 29 14 ∧
      ({3, 13, 23} : Finset ℕ) ⊆ paritySafeActiveSupport 29 56 := by
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd,
    mem_squareAnchorOddActivePrimes]
  decide

theorem shell29_local_card_lower :
    3 ≤ (paritySafeActiveSupport 29 14).card ∧
      3 ≤ (paritySafeActiveSupport 29 56).card := by
  constructor
  · simpa using Finset.card_le_card shell29_support_witnesses.1
  · simpa using Finset.card_le_card shell29_support_witnesses.2

theorem shell29_local_excess_lower :
    2 ≤ (paritySafeActiveSupport 29 14).card - 1 ∧
      2 ≤ (paritySafeActiveSupport 29 56).card - 1 := by
  constructor
  · exact local_support_excess_ge_of_card_ge shell29_local_card_lower.1
  · exact local_support_excess_ge_of_card_ge shell29_local_card_lower.2

theorem shell29_supportExcess_ge_four : 4 ≤ paritySafeSupportExcess 29 :=
  two_seat_support_card_lower_le_supportExcess shell29_candidate_seats.1
    shell29_candidate_seats.2 (by decide) shell29_local_card_lower.1 shell29_local_card_lower.2

theorem shell29_pair_cap_and_candidate :
    paritySafeTwoPrimeIncidenceUpper 29 = 31 ∧
      (squareAnchorOddPointCoprimeOffsets 29).card = 28 := by
  rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

theorem shell29_uncovered_ge_one : 1 ≤ (paritySafeUncoveredCandidates 29).card := by
  have h := paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper
    29 4 shell29_supportExcess_ge_four
  simpa only [shell29_pair_cap_and_candidate.1, shell29_pair_cap_and_candidate.2] using h

theorem shell29_uncovered_nonempty : (paritySafeUncoveredCandidates 29).Nonempty :=
  Finset.card_pos.mp shell29_uncovered_ge_one

theorem shell29_prime : ∃ p, Nat.Prime p ∧ 29 ^ 2 < p ∧ p < 30 ^ 2 :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty (by decide) shell29_uncovered_nonempty

end DkMathTest.LegendreHybridProvider
