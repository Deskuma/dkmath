/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreMergedCRTData

#print "file: DkMathTest.NumberTheory.LegendreMergedCRT"

namespace DkMathTest.LegendreMergedCRT

open DkMath.NumberTheory.Legendre DkMathTest.LegendreHybridClassification
open DkMathTest.LegendreHybridProvider DkMathTest.LegendreBlockLocalization
open scoped BigOperators

set_option maxRecDepth 100000

/-- This is only support in the controlled basis, not the full active support. -/
def restrictedWitness (tag n r : ℕ) : Finset ℕ :=
  (controlledBasis tag).filter (fun q => ¬q ∣ n ∧ q ∣ n ^ 2 + r)

set_option maxHeartbeats 12000000 in
-- Check the explicitly supplied family labels and candidate conditions at34 checkpoints.
theorem checkpoint_families_realized :
    ∀ t ∈ checkpointData, ∀ j ∈ familyData t.1 t.2.1,
      j.1 ∈ squareAnchorOddPointCoprimeOffsets t.2.1 ∧
      j.2 ⊆ paritySafeActiveSupport t.2.1 j.1 ∧
      j.2 ⊆ controlledBasis t.1 ∧ (j.2.card = 2 ∨ j.2.card = 3) ∧
      (∏ q ∈ j.2, q) ∣ t.2.1 ^ 2 + j.1 := by
  simp only [candidate_eq_filter_Icc, Finset.subset_iff,
    mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Reduce unions and charge sums for the34 finite certificate tables.
theorem checkpoint_charge_checked :
    ∀ t ∈ checkpointData,
      mergedSeatCharge (familyData t.1 t.2.1) Prod.fst Prod.snd = t.2.2.2.2 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all bounded window seats against only the selected7/10 prime labels.
/-- The finite pair/triple pool saturates exactly the controlled multi-support seats and labels. -/
theorem checkpoint_restricted_saturation_checked :
    ∀ t ∈ checkpointData,
      (familyData t.1 t.2.1).image Prod.fst =
        (Finset.Icc 1 (2 * t.2.1)).filter (fun r =>
          Nat.Coprime t.2.1 r ∧ Odd (t.2.1 ^ 2 + r) ∧
          2 ≤ (restrictedWitness t.1 t.2.1 r).card) ∧
      ∀ r ∈ (familyData t.1 t.2.1).image Prod.fst,
        mergedSeatWitness (familyData t.1 t.2.1) Prod.fst Prod.snd r =
          restrictedWitness t.1 t.2.1 r := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Inspect the finite raw-index sums and short-product subpool unions.
theorem checkpoint_index_and_short_charge_checked :
    ∀ t ∈ comparisonData,
      (∑ j ∈ familyData t.1 t.2.1, (j.2.card - 1)) = t.2.2.1 ∧
      mergedSeatCharge ((familyData t.1 t.2.1).filter
        (fun j => (∏ q ∈ j.2, q) < t.2.1)) Prod.fst Prod.snd = t.2.2.2 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Normalize the existing structural caps and candidate filters through anchor503.
theorem extra_caps_checked :
    ∀ t ∈ extraCapData,
      paritySafeTwoPrimeIncidenceUpper t.1 = t.2.1 ∧
      (squareAnchorOddPointCoprimeOffsets t.1).card = t.2.2 := by
  simp_rw [twoPrimeUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Transport cap/candidate facts between the checked tuple tables without recomputing incidence.
theorem checkpoint_caps_checked :
    ∀ t ∈ checkpointData,
      paritySafeTwoPrimeIncidenceUpper t.2.1 = t.2.2.1 ∧
      (squareAnchorOddPointCoprimeOffsets t.2.1).card = t.2.2.2.1 := by
  intro t ht
  have hmatch : ∀ u ∈ checkpointData,
      (u.2.1, u.2.2.1, u.2.2.2.1) ∈ classTwoData ∪ extraCapData := by decide +kernel
  rcases Finset.mem_union.mp (hmatch t ht) with hold | hnew
  · exact classification_caps_checked (t.2.1, t.2.2.1, t.2.2.2.1)
      (Finset.mem_union.mpr (Or.inr hold))
  · exact extra_caps_checked (t.2.1, t.2.2.1, t.2.2.2.1) hnew

theorem checkpoint_charge_le_excess :
    ∀ t ∈ checkpointData, t.2.2.2.2 ≤ paritySafeSupportExcess t.2.1 := by
  intro t ht
  rw [← checkpoint_charge_checked t ht]
  apply mergedSeatCharge_le_supportExcess (familyData t.1 t.2.1) Prod.fst Prod.snd
  · exact fun j hj => (checkpoint_families_realized t ht j hj).1
  · exact fun j hj => (checkpoint_families_realized t ht j hj).2.1

theorem checkpoint_uncovered_lower :
    ∀ t ∈ checkpointData,
      t.2.2.2.1 + t.2.2.2.2 - t.2.2.1 ≤ (paritySafeUncoveredCandidates t.2.1).card := by
  intro t ht
  obtain ⟨hb, ha⟩ := checkpoint_caps_checked t ht
  simpa only [hb, ha] using paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper
    t.2.1 t.2.2.2.2 (checkpoint_charge_le_excess t ht)

theorem checkpoint_prime_of_demand_met :
    ∀ t ∈ checkpointData, t.2.2.1 < t.2.2.2.1 + t.2.2.2.2 →
      ∃ p, Nat.Prime p ∧ SquareCell t.2.1 p := by
  intro t ht hgap
  have hn : ∀ u ∈ checkpointData, 0 < u.2.1 := by decide +kernel
  apply prime_squareCell_of_merged_certificates (hn t ht) (familyData t.1 t.2.1) Prod.fst Prod.snd
  · exact fun j hj => (checkpoint_families_realized t ht j hj).1
  · exact fun j hj => (checkpoint_families_realized t ht j hj).2.1
  · obtain ⟨hb, ha⟩ := checkpoint_caps_checked t ht
    rwa [hb, ha, checkpoint_charge_checked t ht]

theorem survivor_recount_checked :
    ((checkpointData.filter (fun t => t.1 = 7 ∧ t.2.2.1 < t.2.2.2.1 + t.2.2.2.2)).image
      (fun t => t.2.1)) ∩ LegendreAdaptiveClassification.unresolvedShells =
      LegendreAdaptiveClassification.unresolvedShells.erase 97 ∧
    (LegendreAdaptiveClassification.unresolvedShells.erase 97).card = 24 ∧
    ∀ n ∈ LegendreAdaptiveClassification.unresolvedShells, ∃ t ∈ checkpointData,
      t.2.1 = n ∧ t.2.2.1 < t.2.2.2.1 + t.2.2.2.2 := by
  decide +kernel

theorem all_previous_survivors_prime :
    ∀ n ∈ LegendreAdaptiveClassification.unresolvedShells,
      ∃ p, Nat.Prime p ∧ SquareCell n p := by
  intro n hn
  obtain ⟨t, ht, heq, hgap⟩ := survivor_recount_checked.2.2 n hn
  simpa only [heq] using checkpoint_prime_of_demand_met t ht hgap

theorem shell58_uncovered_ge_eight : 8 ≤ (paritySafeUncoveredCandidates 58).card := by
  exact checkpoint_uncovered_lower (7, 58, 63, 56, 15) (by decide)

theorem shell68_uncovered_ge_ten : 10 ≤ (paritySafeUncoveredCandidates 68).card := by
  exact checkpoint_uncovered_lower (7, 68, 70, 64, 16) (by decide)

theorem shell58_prime : ∃ p, Nat.Prime p ∧ 58 ^ 2 < p ∧ p < 59 ^ 2 :=
  checkpoint_prime_of_demand_met (7, 58, 63, 56, 15) (by decide) (by decide)

theorem shell68_prime : ∃ p, Nat.Prime p ∧ 68 ^ 2 < p ∧ p < 69 ^ 2 :=
  checkpoint_prime_of_demand_met (7, 68, 70, 64, 16) (by decide) (by decide)

theorem shell97_expanded_prime : ∃ p, Nat.Prime p ∧ SquareCell 97 p :=
  checkpoint_prime_of_demand_met (10, 97, 125, 96, 35) (by decide) (by decide)

theorem shell107_expanded_prime : ∃ p, Nat.Prime p ∧ SquareCell 107 p :=
  checkpoint_prime_of_demand_met (10, 107, 144, 106, 42) (by decide) (by decide)

theorem shell127_expanded_prime : ∃ p, Nat.Prime p ∧ SquareCell 127 p :=
  checkpoint_prime_of_demand_met (10, 127, 170, 126, 46) (by decide) (by decide)

/-- The stronger mixed-anchor selector's guaranteed pair/triple ranges are all empty here. -/
theorem mixed_short_period_budget_zero :
    ∀ t ∈ mixedAnchorData,
      t.1 = 2 ^ t.2.1 * t.2.2.1 ^ t.2.2.2 ∧ (t.2.2.1).Prime ∧ 0 < t.2.2.2 ∧
      ∀ Q ∈ (controlledBasis 7).powerset,
        (Q.card = 2 ∨ Q.card = 3) → (∀ q ∈ Q, ¬q ∣ t.1) →
        t.1 / (t.2.2.1 * (∏ q ∈ Q, q)) = 0 := by
  decide +kernel

/-- Under the checked fixed pools, the four final large-checkpoint certificates do not meet demand. -/
theorem large_checkpoint_charge_deficits :
    ∀ t ∈ checkpointData, t.2.1 = 211 ∨ t.2.1 = 503 →
      t.2.2.2.1 + t.2.2.2.2 ≤ t.2.2.1 := by
  decide +kernel

theorem prime_checkpoints_checked :
    ∀ n ∈ ({47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 107, 127, 211, 503} : Finset ℕ),
      Nat.Prime n := by
  decide +kernel

theorem controlled_basis_prime_checked :
    ∀ tag ∈ ({7, 10} : Finset ℕ), ∀ q ∈ controlledBasis tag, q.Prime ∧ q ≠ 2 := by
  decide +kernel

/-- Keep exactly the first floor-many positive parity lifts of each witness product. -/
def floorFamilies (tag n : ℕ) : Finset (ℕ × Finset ℕ) :=
  (familyData tag n).filter (fun j =>
    j.1 ≤ 2 * (∏ q ∈ j.2, q) * ((n - 1) / (∏ q ∈ j.2, q)))

set_option maxHeartbeats 12000000 in
-- Count and merge the guaranteed finite lift prefixes on prime checkpoints.
theorem checkpoint_floor_charges_checked :
    ∀ t ∈ floorComparisonData,
      (∑ j ∈ floorFamilies t.1 t.2.1, (j.2.card - 1)) = t.2.2.1 ∧
      mergedSeatCharge (floorFamilies t.1 t.2.1) Prod.fst Prod.snd = t.2.2.2 := by
  decide +kernel

end DkMathTest.LegendreMergedCRT
