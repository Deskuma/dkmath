/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCRTSeat
import DkMathTest.NumberTheory.LegendreAdaptiveCertificate

#print "file: DkMathTest.NumberTheory.LegendreCRTSeat"

namespace DkMathTest.LegendreCRTSeat

open DkMath.NumberTheory.Legendre DkMathTest.LegendreBlockLocalization
open DkMathTest.LegendreAdaptiveCertificate
open scoped BigOperators

/-- A zero residue needs the positive endpoint representative, not offset0. -/
theorem zero_residue_positive_endpoint :
    (3 : ℕ) ∈ Finset.Icc 1 3 ∧ Nat.ModEq 3 3 0 ∧
      ¬∃ r ∈ Finset.Icc 1 2, Nat.ModEq 3 r 0 := by
  decide

/-- Raw period21 fits22 but does not supply a parity-compatible point at prime anchor11. -/
theorem raw_period_does_not_guarantee_parity :
    ({3, 7} : Finset ℕ) ⊆ squareAnchorOddActivePrimes 11 ∧ (21 : ℕ) ≤ 2 * 11 ∧
      ¬∃ r ∈ Finset.Icc 1 (2 * 11), Odd (11 ^ 2 + r) ∧ 21 ∣ 11 ^ 2 + r := by
  simp only [Finset.subset_iff, mem_squareAnchorOddActivePrimes, Nat.odd_iff]
  decide

/-- Even the parity-adjusted period10 fitting12 does not ensure anchor coprimality at6. -/
theorem parity_period_does_not_guarantee_candidate :
    (5 : ℕ) ∈ squareAnchorOddActivePrimes 6 ∧ 2 * 5 ≤ 2 * 6 ∧
      (∃ r ∈ Finset.Icc 1 (2 * 6), Odd (6 ^ 2 + r) ∧ 5 ∣ 6 ^ 2 + r) ∧
      ¬∃ r ∈ squareAnchorOddPointCoprimeOffsets 6, 5 ∣ 6 ^ 2 + r := by
  rw [candidate_eq_filter_Icc]
  simp only [mem_squareAnchorOddActivePrimes, Nat.odd_iff]
  decide

/-- Distinct support subsets may be realized at the very same actual candidate seat. -/
theorem distinct_witness_sets_do_not_separate_seats :
    ({3, 5} : Finset ℕ) ≠ {3, 23} ∧
      (44 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 41 ∧
      ({3, 5} : Finset ℕ) ⊆ paritySafeActiveSupport 41 44 ∧
      ({3, 23} : Finset ℕ) ⊆ paritySafeActiveSupport 41 44 := by
  rw [candidate_eq_filter_Icc]
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide

theorem prime107_short_period_candidate :
    (206 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 107 ∧
      ({3, 5, 7} : Finset ℕ) ⊆ paritySafeActiveSupport 107 206 ∧
      (∏ q ∈ ({3, 5, 7} : Finset ℕ), q) < 107 := by
  rw [candidate_eq_filter_Icc]
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide

theorem prime107_structural_charge : 2 ≤ paritySafeSupportExcess 107 :=
  supportExcess_ge_two_of_prime_gt_105 (by decide) (by decide)

set_option maxRecDepth 20000 in
/-- One fixed CRT class can pay at two distinct seats through different parity-compatible lifts. -/
theorem prime211_period_lift_seats :
    (104 : ℕ) ≠ 314 ∧
      (104 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 211 ∧
      (314 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 211 ∧
      ({3, 5, 7} : Finset ℕ) ⊆ paritySafeActiveSupport 211 104 ∧
      ({3, 5, 7} : Finset ℕ) ⊆ paritySafeActiveSupport 211 314 := by
  rw [candidate_eq_filter_Icc]
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide +kernel

set_option maxRecDepth 20000 in
theorem prime211_structural_family_charge : 4 ≤ paritySafeSupportExcess 211 := by
  have hQ : ({3, 5, 7} : Finset ℕ) ⊆ squareAnchorOddActivePrimes 211 := by
    simp only [Finset.subset_iff, mem_squareAnchorOddActivePrimes]
    decide
  simpa using prime_anchor_period_family_charge_le_supportExcess
    (by decide +kernel : Nat.Prime 211) {3, 5, 7} hQ

set_option maxRecDepth 20000 in
/-- The infinite charge2 provider is insufficient for the checked demand at107. -/
theorem prime107_provider_needs_more_charge :
    paritySafeTwoPrimeIncidenceUpper 107 = 144 ∧
      (squareAnchorOddPointCoprimeOffsets 107).card = 106 ∧
      ¬paritySafeTwoPrimeIncidenceUpper 107 < (squareAnchorOddPointCoprimeOffsets 107).card + 2 := by
  simp_rw [DkMathTest.LegendreHybridProvider.twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

/-- Instantiate the indexed congruence consumer with the actual distinct seats from the mandatory case. -/
theorem shell41_indexed_CRT_prime : ∃ p, Nat.Prime p ∧ 41 ^ 2 < p ∧ p < 42 ^ 2 := by
  apply exists_prime_squareCell_of_indexed_modEq_certificates
    (n := 41) (by decide) shell41Seats id shell41Witness
  · intro a _ b _ hab
    exact hab
  · exact fun r hr => shell41_candidate_seats hr
  · intro r hr q hq
    exact (mem_paritySafeActiveSupport_iff_dvd.mp (shell41_support_witnesses r hr hq)).1
  · intro r hr q hq
    exact Nat.modEq_zero_iff_dvd.mpr
      (mem_paritySafeActiveSupport_iff_dvd.mp (shell41_support_witnesses r hr hq)).2
  · rw [shell41_cap_and_candidate.1, shell41_cap_and_candidate.2, shell41_witness_charge]
    decide

end DkMathTest.LegendreCRTSeat
