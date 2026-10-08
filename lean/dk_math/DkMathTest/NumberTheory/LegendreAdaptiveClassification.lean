/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreAdaptiveClassificationData

#print "file: DkMathTest.NumberTheory.LegendreAdaptiveClassification"

namespace DkMathTest.LegendreAdaptiveClassification

open DkMath.NumberTheory.Legendre DkMathTest.LegendreHybridClassification
open scoped BigOperators

def diagnosticSeats (n : ℕ) : Finset ℕ :=
  (diagnosticWitnessData.filter (fun t => t.1 = n)).image (fun t => t.2.1)

def diagnosticWitness (n r : ℕ) : Finset ℕ :=
  (diagnosticWitnessData.filter (fun t => t.1 = n ∧ t.2.1 = r)).biUnion (fun t => t.2.2)

set_option maxRecDepth 40000

theorem diagnostic_partition_checked :
    diagnosticData.card = 30 ∧ solvedUpToFive.card = 4 ∧ solvedAtSix.card = 1 ∧ unresolvedShells.card = 25 ∧
    diagnosticData.image Prod.fst = classTwoData.image Prod.fst ∧
    solvedUpToFive ∪ solvedAtSix ∪ unresolvedShells = classTwoData.image Prod.fst ∧
    Disjoint solvedUpToFive solvedAtSix ∧ Disjoint (solvedUpToFive ∪ solvedAtSix) unresolvedShells := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check only three seats per shell and the supplied at-most-three support primes.
theorem diagnostic_certificates_checked :
    ∀ t ∈ diagnosticData,
      diagnosticSeats t.1 ⊆ squareAnchorOddPointCoprimeOffsets t.1 ∧
      (∀ r ∈ diagnosticSeats t.1, diagnosticWitness t.1 r ⊆ paritySafeActiveSupport t.1 r) ∧
      (diagnosticSeats t.1).card = 3 ∧
      (∀ r ∈ diagnosticSeats t.1, (diagnosticWitness t.1 r).card ≤ 3) ∧
      (∑ r ∈ diagnosticSeats t.1, ((diagnosticWitness t.1 r).card - 1)) = t.2.2.2 := by
  simp only [DkMathTest.LegendreBlockLocalization.candidate_eq_filter_Icc,
    Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide +kernel

theorem diagnostic_caps_match_prior :
    ∀ t ∈ diagnosticData,
      paritySafeTwoPrimeIncidenceUpper t.1 = t.2.1 ∧
      (squareAnchorOddPointCoprimeOffsets t.1).card = t.2.2.1 := by
  intro t ht
  have hm : ∀ u ∈ diagnosticData, (u.1, u.2.1, u.2.2.1) ∈ classTwoData := by decide +kernel
  exact classification_caps_checked (t.1, t.2.1, t.2.2.1) (Finset.mem_union.mpr (Or.inr (hm t ht)))

theorem diagnostic_charge_le_excess :
    ∀ t ∈ diagnosticData, t.2.2.2 ≤ paritySafeSupportExcess t.1 := by
  intro t ht
  obtain ⟨hR, hP, _, _, hcost⟩ := diagnostic_certificates_checked t ht
  have h := sum_witness_support_excess_le_supportExcess (diagnosticSeats t.1)
    (diagnosticWitness t.1) hR hP
  simpa only [hcost] using h

theorem diagnostic_success_condition_checked :
    ∀ t ∈ diagnosticData,
      (t.1 ∈ solvedUpToFive ↔ t.2.1 < t.2.2.1 + t.2.2.2 ∧ t.2.2.2 ≤ 5) ∧
      (t.1 ∈ solvedAtSix ↔ t.2.1 < t.2.2.1 + t.2.2.2 ∧ t.2.2.2 = 6) ∧
      (t.1 ∈ unresolvedShells ↔ t.2.2.1 + 6 ≤ t.2.1 ∧ t.2.2.2 = 6) := by
  decide +kernel

theorem diagnostic_solved_uncovered :
    ∀ t ∈ diagnosticData, t.1 ∈ solvedUpToFive ∪ solvedAtSix →
      (paritySafeUncoveredCandidates t.1).Nonempty := by
  intro t ht hs
  obtain ⟨hb, ha⟩ := diagnostic_caps_match_prior t ht
  apply paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess (diagnostic_charge_le_excess t ht)
  rw [hb, ha]
  rcases Finset.mem_union.mp hs with hs | hs
  · exact ((diagnostic_success_condition_checked t ht).1.mp hs).1
  · exact ((diagnostic_success_condition_checked t ht).2.1.mp hs).1

theorem diagnostic_solved_prime :
    ∀ t ∈ diagnosticData, t.1 ∈ solvedUpToFive ∪ solvedAtSix →
      ∃ p, Nat.Prime p ∧ SquareCell t.1 p := by
  intro t ht hs
  have hn : ∀ u ∈ diagnosticData, 0 < u.1 := by decide +kernel
  exact exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty (hn t ht)
    (diagnostic_solved_uncovered t ht hs)

theorem diagnostic_survivor_budget_obstruction :
    ∀ t ∈ diagnosticData, t.1 ∈ unresolvedShells → ∀ e ≤ 6,
      ¬paritySafeTwoPrimeIncidenceUpper t.1 < (squareAnchorOddPointCoprimeOffsets t.1).card + e := by
  intro t ht hs e he
  obtain ⟨hb, ha⟩ := diagnostic_caps_match_prior t ht
  rw [hb, ha]
  have hbound := ((diagnostic_success_condition_checked t ht).2.2.mp hs).1
  omega

theorem diagnostic_survivor_charge_ge_six :
    ∀ t ∈ diagnosticData, t.1 ∈ unresolvedShells → 6 ≤ paritySafeSupportExcess t.1 := by
  intro t ht hs
  have heq := ((diagnostic_success_condition_checked t ht).2.2.mp hs).2
  rw [← heq]
  exact diagnostic_charge_le_excess t ht

theorem diagnostic_survivors_have_few_odd_anchor_factors :
    ∀ n ∈ unresolvedShells, (n.primeFactors.erase 2).card ≤ 1 := by
  decide +kernel

end DkMathTest.LegendreAdaptiveClassification
