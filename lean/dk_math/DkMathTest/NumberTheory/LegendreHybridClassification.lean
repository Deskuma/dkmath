/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreHybridClassificationData

#print "file: DkMathTest.NumberTheory.LegendreHybridClassification"

namespace DkMathTest.LegendreHybridClassification

open DkMath.NumberTheory.Legendre DkMathTest.LegendreHybridProvider
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators

-- All finite floor/prime-factor data below are independently reduced by the kernel.
set_option maxRecDepth 40000

set_option maxHeartbeats 4000000 in
-- Normalize floor caps and candidate filters for all99 recorded shells.
theorem classification_caps_checked :
    (∀ t ∈ classZeroData ∪ classOneData ∪ classTwoData,
      paritySafeTwoPrimeIncidenceUpper t.1 = t.2.1 ∧
      (squareAnchorOddPointCoprimeOffsets t.1).card = t.2.2) := by
  simp_rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

theorem classification_partition_checked :
    classZeroData.card = 59 ∧ classOneData.card = 10 ∧ classTwoData.card = 30 ∧
    (classZeroData.image Prod.fst ∪ classOneData.image Prod.fst ∪ classTwoData.image Prod.fst) =
      Finset.Icc 2 100 ∧
    Disjoint (classZeroData.image Prod.fst) (classOneData.image Prod.fst) ∧
    Disjoint (classZeroData.image Prod.fst ∪ classOneData.image Prod.fst)
      (classTwoData.image Prod.fst) ∧
    classOneCertificates.image Prod.fst = classOneData.image Prod.fst := by
  decide +kernel

/-- Check actual candidates and only the supplied support primes, never a whole excess sum. -/
theorem class_one_certificates_checked :
    ∀ c ∈ classOneCertificates,
      c.2.1.1 ≠ c.2.2.1 ∧
      c.2.1.1 ∈ squareAnchorOddPointCoprimeOffsets c.1 ∧
      c.2.2.1 ∈ squareAnchorOddPointCoprimeOffsets c.1 ∧
      c.2.1.2.card = 3 ∧ c.2.2.2.card = 3 ∧
      c.2.1.2 ⊆ paritySafeActiveSupport c.1 c.2.1.1 ∧
      c.2.2.2 ⊆ paritySafeActiveSupport c.1 c.2.2.1 := by
  simp only [candidate_eq_filter_Icc, Finset.subset_iff,
    mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide +kernel

theorem class_one_certified_excess :
    ∀ c ∈ classOneCertificates, 4 ≤ paritySafeSupportExcess c.1 := by
  intro c hc
  obtain ⟨hne, hr, hs, hp, hq, hpr, hqs⟩ := class_one_certificates_checked c hc
  have hkr : 3 ≤ (paritySafeActiveSupport c.1 c.2.1.1).card := by
    rw [← hp]
    exact Finset.card_le_card hpr
  have hls : 3 ≤ (paritySafeActiveSupport c.1 c.2.2.1).card := by
    rw [← hq]
    exact Finset.card_le_card hqs
  exact two_seat_support_card_lower_le_supportExcess hr hs hne hkr hls

set_option maxHeartbeats 4000000 in
-- Check the ten finite hybrid thresholds without computing whole-shell excess.
theorem class_one_gap_checked :
    ∀ c ∈ classOneCertificates,
      (squareAnchorOddPointCoprimeOffsets c.1).card ≤ paritySafeTwoPrimeIncidenceUpper c.1 ∧
      paritySafeTwoPrimeIncidenceUpper c.1 < (squareAnchorOddPointCoprimeOffsets c.1).card + 4 := by
  simp_rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

theorem class_one_uncovered :
    ∀ c ∈ classOneCertificates, (paritySafeUncoveredCandidates c.1).Nonempty := by
  intro c hc
  exact paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    (class_one_certified_excess c hc) (class_one_gap_checked c hc).2

theorem class_one_prime :
    ∀ c ∈ classOneCertificates, ∃ p, Nat.Prime p ∧ SquareCell c.1 p := by
  intro c hc
  apply exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty
  · have hn : ∀ d ∈ classOneCertificates, 0 < d.1 := by decide +kernel
    exact hn c hc
  · exact class_one_uncovered c hc

theorem class_zero_uncovered :
    ∀ t ∈ classZeroData, (paritySafeUncoveredCandidates t.1).Nonempty := by
  intro t ht
  have h := classification_caps_checked t
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ht))))
  apply paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess (e := 0) (by omega)
  rw [h.1, h.2, Nat.add_zero]
  have hh : ∀ u ∈ classZeroData, u.2.1 < u.2.2 := by decide +kernel
  exact hh t ht

theorem class_zero_prime :
    ∀ t ∈ classZeroData, ∃ p, Nat.Prime p ∧ SquareCell t.1 p := by
  intro t ht
  apply exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty
  · have hn : ∀ u ∈ classZeroData, 0 < u.1 := by decide +kernel
    exact hn t ht
  · exact class_zero_uncovered t ht

def gainShellData : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(77, 66, 62, 60), (85, 71, 67, 64), (95, 76, 70, 72)}

/-- With the same maximum local cost4, exactly these new cap examples cross the old failure boundary. -/
theorem gain_shells_checked :
    ∀ t ∈ gainShellData,
      paritySafeIncidenceUpper t.1 = t.2.1 ∧
      paritySafeTwoPrimeIncidenceUpper t.1 = t.2.2.1 ∧
      (squareAnchorOddPointCoprimeOffsets t.1).card = t.2.2.2 ∧
      ¬paritySafeIncidenceUpper t.1 < (squareAnchorOddPointCoprimeOffsets t.1).card + 4 ∧
      paritySafeTwoPrimeIncidenceUpper t.1 < (squareAnchorOddPointCoprimeOffsets t.1).card + 4 := by
  simp_rw [DkMathTest.LegendreIncidenceUpper.incidenceUpper_eq_finite,
    twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

/-- Class2 means the budget<=4 cannot satisfy the sufficient deficit criterion. -/
theorem class_two_budget_obstruction :
    ∀ t ∈ classTwoData, ∀ e ≤ 4,
      ¬ paritySafeTwoPrimeIncidenceUpper t.1 < (squareAnchorOddPointCoprimeOffsets t.1).card + e := by
  intro t ht e he
  have h := classification_caps_checked t (Finset.mem_union.mpr (Or.inr ht))
  rw [h.1, h.2]
  have hh : ∀ u ∈ classTwoData, u.2.2 + 4 ≤ u.2.1 := by decide +kernel
  have := hh t ht
  omega

/-- Two distinct odd anchor primes do not suffice to make the zero-excess criterion true. -/
theorem two_odd_anchor_primes_zero_excess_counterexample :
    ((77 : ℕ).primeFactors.erase 2).card = 2 ∧
      paritySafeTwoPrimeIncidenceUpper 77 = 62 ∧
      (squareAnchorOddPointCoprimeOffsets 77).card = 60 := by
  simp_rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

/-- Even the fixed two-seat/three-prime budget fails with two distinct odd anchor factors. -/
theorem two_odd_anchor_primes_small_certificate_counterexample :
    ((91 : ℕ).primeFactors.erase 2).card = 2 ∧
      paritySafeTwoPrimeIncidenceUpper 91 = 76 ∧
      (squareAnchorOddPointCoprimeOffsets 91).card = 72 := by
  simp_rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

end DkMathTest.LegendreHybridClassification
