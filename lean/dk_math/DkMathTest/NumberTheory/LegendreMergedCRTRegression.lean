/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeMixedCRT
import DkMathTest.NumberTheory.LegendreHybridProvider
import DkMathTest.NumberTheory.LegendreMergedCRT

#print "file: DkMathTest.NumberTheory.LegendreMergedCRTRegression"

namespace DkMathTest.LegendreMergedCRTRegression

open DkMath.NumberTheory.Legendre DkMathTest.LegendreHybridProvider
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators

set_option maxRecDepth 20000

/-- Disjoint sets gain one; one shared label preserves the sum; identical pairs lose one. -/
theorem local_overlap_charge_cases :
    (({3, 5} ∪ {7, 11} : Finset ℕ).card - 1) = 3 ∧
    (({3, 5} ∪ {3, 7} : Finset ℕ).card - 1) = 2 ∧
    (({3, 5} ∪ {3, 5} : Finset ℕ).card - 1) = 1 := by
  decide

/-- Actual support charge1 at anchor8 is overcounted by two identical family indices. -/
theorem naive_noninjective_charge_counterexample :
    (11 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 8 ∧
    ({3, 5} : Finset ℕ) ⊆ paritySafeActiveSupport 8 11 ∧
    mergedSeatCharge (Finset.range 2) (fun _ => 11) (fun _ => {3, 5}) = 1 ∧
    paritySafeSupportExcess 8 = 1 ∧
    paritySafeSupportExcess 8 < ∑ _j ∈ Finset.range 2, (({3, 5} : Finset ℕ).card - 1) := by
  have hc : ({1, 5, 11, 13} : Finset ℕ) ⊆ squareAnchorOddPointCoprimeOffsets 8 := by
    rw [candidate_eq_filter_Icc]
    decide
  have hw : ∀ r ∈ ({1, 5, 11, 13} : Finset ℕ),
      ∃ q ∈ ({3, 5, 7} : Finset ℕ), q ∈ paritySafeActiveSupport 8 r := by
    simp only [mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
    decide
  have hcovered : ({1, 5, 11, 13} : Finset ℕ) ⊆ paritySafeCoveredCandidates 8 := by
    intro r hr
    obtain ⟨q, _, hq⟩ := hw r hr
    exact mem_paritySafeCoveredCandidates.mpr ⟨hc hr, q, hq⟩
  have hfour : 4 ≤ (paritySafeCoveredCandidates 8).card := by
    simpa using Finset.card_le_card hcovered
  have hB : paritySafeTwoPrimeIncidenceUpper 8 = 5 := by
    rw [twoPrimeUpper_eq_finite]
    decide +kernel
  have hcap := paritySafeIncidenceCount_le_twoPrimeUpper 8
  have hledger := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence 8
  have hupper : paritySafeSupportExcess 8 ≤ 1 := by omega
  have hseat : (11 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 8 := hc (by decide)
  have hQ : ({3, 5} : Finset ℕ) ⊆ paritySafeActiveSupport 8 11 := by
    simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
    decide
  have hcharge : mergedSeatCharge (Finset.range 2) (fun _ => 11) (fun _ => {3, 5}) = 1 := by
    decide
  have hlower := mergedSeatCharge_le_supportExcess (Finset.range 2) (fun _ => 11) (fun _ => {3, 5})
    (fun _ _ => hseat) (fun _ _ => hQ)
  have heq : paritySafeSupportExcess 8 = 1 := by omega
  refine ⟨hseat, hQ, hcharge, heq, ?_⟩
  rw [heq]
  decide

theorem prime107_two_star_families_charge : 12 ≤ paritySafeSupportExcess 107 := by
  simpa using prime_star_pair_charge_le_supportExcess (by decide : Nat.Prime 107) (by decide)

/-- The mixed selector can supply positive counted charge outside the small diagnostic anchors. -/
theorem mixed320_counted_charge : 3 ≤ paritySafeSupportExcess 320 := by
  have hQ : ({3, 7} : Finset ℕ) ⊆ squareAnchorOddActivePrimes 320 := by
    simp only [Finset.subset_iff, mem_squareAnchorOddActivePrimes]
    decide
  simpa using mixed_anchor_period_family_charge_le_supportExcess
    (n := 320) (p := 5) (a := 6) (k := 1) (by decide) (by decide) (by decide) {3, 7} hQ

theorem mixed320_explicit_lifts :
    ({101, 311, 521} : Finset ℕ) ⊆ squareAnchorOddPointCoprimeOffsets 320 ∧
    ∀ r ∈ ({101, 311, 521} : Finset ℕ),
      ({3, 7} : Finset ℕ) ⊆ paritySafeActiveSupport 320 r ∧
      Nat.ModEq 10 (320 ^ 2 + r) 1 := by
  rw [candidate_eq_filter_Icc]
  simp only [Finset.subset_iff, mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Transport the checked floor prefixes as subsets of the realized finite families.
theorem checkpoint_floor_charge_le_excess :
    ∀ t ∈ DkMathTest.LegendreMergedCRT.floorComparisonData,
      t.2.2.2 ≤ paritySafeSupportExcess t.2.1 := by
  open DkMathTest.LegendreMergedCRT in
  intro t ht
  have hmatch : ∀ u ∈ floorComparisonData, ∃ v ∈ checkpointData,
      v.1 = u.1 ∧ v.2.1 = u.2.1 := by decide +kernel
  obtain ⟨v, hv, htag, hn⟩ := hmatch t ht
  rw [← (checkpoint_floor_charges_checked t ht).2]
  have hreal : ∀ j ∈ floorFamilies t.1 t.2.1,
      j.1 ∈ squareAnchorOddPointCoprimeOffsets t.2.1 ∧
      j.2 ⊆ paritySafeActiveSupport t.2.1 j.1 := by
    intro j hj
    have hjfull : j ∈ familyData t.1 t.2.1 := (Finset.mem_filter.mp hj).1
    have h := checkpoint_families_realized v hv j (by simpa only [htag, hn] using hjfull)
    simpa only [htag, hn] using And.intro h.1 h.2.1
  exact mergedSeatCharge_le_supportExcess (floorFamilies t.1 t.2.1) Prod.fst Prod.snd
    (fun j hj => (hreal j hj).1) (fun j hj => (hreal j hj).2)

end DkMathTest.LegendreMergedCRTRegression
