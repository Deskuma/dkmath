/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreHybridClassification

#print "file: DkMathTest.NumberTheory.LegendreAdaptiveCertificate"

namespace DkMathTest.LegendreAdaptiveCertificate

open DkMath.NumberTheory.Legendre DkMathTest.LegendreHybridProvider
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators

def shell41Seats : Finset ℕ := {2, 24, 44}

def shell41Witness (r : ℕ) : Finset ℕ :=
  if r = 2 then {3, 11, 17} else if r = 24 then {5, 11, 31} else {3, 5, 23}

def shell91Seats : Finset ℕ := {38, 44, 68}

def shell91Witness (r : ℕ) : Finset ℕ :=
  if r = 38 then {3, 47, 59} else if r = 44 then {3, 5, 37} else {3, 11, 23}

theorem shell41_candidate_seats : shell41Seats ⊆ squareAnchorOddPointCoprimeOffsets 41 := by
  rw [candidate_eq_filter_Icc]
  decide

theorem shell41_support_witnesses :
    ∀ r ∈ shell41Seats, shell41Witness r ⊆ paritySafeActiveSupport 41 r := by
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide

theorem shell41_witness_charge : (∑ r ∈ shell41Seats, ((shell41Witness r).card - 1)) = 6 := by
  decide

theorem shell41_supportExcess_ge_six : 6 ≤ paritySafeSupportExcess 41 := by
  have h := sum_witness_support_excess_le_supportExcess shell41Seats shell41Witness
    shell41_candidate_seats shell41_support_witnesses
  simpa only [shell41_witness_charge] using h

theorem shell41_cap_and_candidate :
    paritySafeTwoPrimeIncidenceUpper 41 = 44 ∧ (squareAnchorOddPointCoprimeOffsets 41).card = 40 := by
  rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

theorem shell41_uncovered_ge_two : 2 ≤ (paritySafeUncoveredCandidates 41).card := by
  have h := paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper
    41 6 shell41_supportExcess_ge_six
  simpa only [shell41_cap_and_candidate.1, shell41_cap_and_candidate.2] using h

theorem shell41_uncovered_nonempty : (paritySafeUncoveredCandidates 41).Nonempty :=
  Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) shell41_uncovered_ge_two)

theorem shell41_prime : ∃ p, Nat.Prime p ∧ 41 ^ 2 < p ∧ p < 42 ^ 2 :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty (by decide) shell41_uncovered_nonempty

theorem shell91_candidate_seats : shell91Seats ⊆ squareAnchorOddPointCoprimeOffsets 91 := by
  rw [candidate_eq_filter_Icc]
  decide

theorem shell91_support_witnesses :
    ∀ r ∈ shell91Seats, shell91Witness r ⊆ paritySafeActiveSupport 91 r := by
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide

theorem shell91_witness_charge : (∑ r ∈ shell91Seats, ((shell91Witness r).card - 1)) = 6 := by
  decide

theorem shell91_supportExcess_ge_six : 6 ≤ paritySafeSupportExcess 91 := by
  have h := sum_witness_support_excess_le_supportExcess shell91Seats shell91Witness
    shell91_candidate_seats shell91_support_witnesses
  simpa only [shell91_witness_charge] using h

theorem shell91_cap_and_candidate :
    paritySafeTwoPrimeIncidenceUpper 91 = 76 ∧ (squareAnchorOddPointCoprimeOffsets 91).card = 72 := by
  rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

theorem shell91_uncovered_ge_two : 2 ≤ (paritySafeUncoveredCandidates 91).card := by
  have h := paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper
    91 6 shell91_supportExcess_ge_six
  simpa only [shell91_cap_and_candidate.1, shell91_cap_and_candidate.2] using h

theorem shell91_uncovered_nonempty : (paritySafeUncoveredCandidates 91).Nonempty :=
  Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) shell91_uncovered_ge_two)

theorem shell91_prime : ∃ p, Nat.Prime p ∧ 91 ^ 2 < p ∧ p < 92 ^ 2 :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty (by decide) shell91_uncovered_nonempty

end DkMathTest.LegendreAdaptiveCertificate
