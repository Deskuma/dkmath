/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount
import DkMathTest.NumberTheory.LegendreHybridProvider

#print "file: DkMathTest.NumberTheory.LegendreCanonicalTailCalibration"

namespace DkMathTest.LegendreCanonicalTailCalibration
open DkMath.NumberTheory.Legendre
open DkMathTest.LegendreHybridProvider DkMathTest.LegendreBlockLocalization
open scoped BigOperators

set_option maxRecDepth 100000
-- Seven-field rows need a larger instance-search expression budget.
set_option synthInstance.maxSize 1024

abbrev RootRow := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- n,A,B2,C3,C5,C7,C11; discovery values are independently kernel-checked below. -/
def rootData : Finset RootRow :=
  {((47,46,54,12,4,4,1):RootRow), ((97,96,125,29,10,7,3):RootRow),
   ((127,126,170,42,11,5,2):RootRow), ((211,210,307,78,27,15,4):RootRow),
   ((503,502,813,222,78,36,8):RootRow), ((1009,1008,1702,460,148,76,27):RootRow),
   ((1013,1012,1721,461,159,79,49):RootRow)}

/-- n,rough seats at11,full rough incidence at11. -/
def roughData : Finset (ℕ × ℕ × ℕ) :=
  {(47,20,7),(97,39,19),(127,52,36),(211,88,61),(503,208,175),(1009,419,402),(1013,421,382)}

def cutoffData : Finset (ℕ × ℕ) := {(47,3),(97,5),(127,5),(211,5),(503,7),(1009,11),(1013,11)}

/-- The first three exclusions' generic union estimate expressed by candidate floor counts. -/
noncomputable def root11UnionFloorLower (n : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 11 < q),
    (primeAnchorProductWaveCount n (11 * q) -
      (primeAnchorProductWaveCount n (33 * q) + primeAnchorProductWaveCount n (55 * q) +
       primeAnchorProductWaveCount n (77 * q)))

def unionData : Finset (ℕ × ℕ × ℕ) := {(47,1,0),(97,3,0),(127,2,0),(211,4,0),
  (503,7,1),(1009,21,6),(1013,46,3)}

set_option maxHeartbeats 16000000 in
-- Reduce only floor/product-wave formulas over all active secondary primes.
theorem root_charges_checked : ∀ t ∈ rootData,
    canonicalRootCharge3 t.1 = t.2.2.2.1 ∧ canonicalRootCharge5 t.1 = t.2.2.2.2.1 ∧
    canonicalRootCharge7 t.1 = t.2.2.2.2.2.1 ∧ canonicalRootCharge11 t.1 = t.2.2.2.2.2.2 := by
  simp_rw [canonicalRootCharge3,canonicalRootCharge5,canonicalRootCharge7,canonicalRootCharge11,
    oddActive_eq_filter_range]
  decide +kernel

set_option maxHeartbeats 18000000 in
-- The old finite structural cap and candidate normal forms, not full E/I.
theorem caps_checked : ∀ t ∈ rootData, t.1.Prime ∧ 11 < t.1 ∧
    (squareAnchorOddPointCoprimeOffsets t.1).card = t.2.1 ∧ paritySafeTwoPrimeIncidenceUpper t.1 = t.2.2.1 := by
  simp_rw [candidate_eq_filter_Icc,twoPrimeUpper_eq_finite]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Direct rough currency is a surviving-wave floor sum, with no canonical minimum computation.
theorem rough_floor_counts_checked : ∀ t ∈ roughData,
    t.1.Prime ∧ 11 < t.1 ∧ primeAnchorAvoidThreeCount t.1 1 - primeAnchorAvoidThreeCount t.1 11 = t.2.1 ∧
      primeAnchorRoughElevenIncidenceCount t.1 = t.2.2 ∧ t.2.2 < t.2.1 := by
  simp_rw [primeAnchorRoughElevenIncidenceCount,oddActive_eq_filter_range]
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Compare exact three-exclusion root11 with the generic union-only formula.
theorem union_credit_checked : ∀ t ∈ unionData,
    root11UnionFloorLower t.1 = t.2.1 ∧ canonicalRootCharge11 t.1 = t.2.1 + t.2.2 := by
  simp_rw [root11UnionFloorLower,canonicalRootCharge11,oddActive_eq_filter_range]
  decide +kernel

/-- Cumulative heads at all four cutoffs, proved from structural exact root formulas. -/
theorem head_charges_checked : ∀ t ∈ rootData,
    (canonicalRootHead t.1 3).card = t.2.2.2.1 ∧
    (canonicalRootHead t.1 5).card = t.2.2.2.1 + t.2.2.2.2.1 ∧
    (canonicalRootHead t.1 7).card = t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 ∧
    (canonicalRootHead t.1 11).card = t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 + t.2.2.2.2.2.2 := by
  intro t ht
  obtain ⟨hn,hlarge,_,_⟩ := caps_checked t ht
  obtain ⟨h3,h5,h7,h11⟩ := root_charges_checked t ht
  simpa only [h3,h5,h7,h11] using canonicalSmallHeads_eq_charges hn hlarge

/-- Least tested cutoff and finite structural-scale comparisons. -/
theorem cutoff_checked : ∀ u ∈ cutoffData, ∃ t ∈ rootData,
    t.1 = u.1 ∧ u.2 ^ 2 ≤ u.1 ∧ u.2 ≤ u.1 ∧
    let D := t.2.2.1 - t.2.1 + 1
    (u.2=3 ∧ D ≤ t.2.2.2.1) ∨
    (u.2=5 ∧ t.2.2.2.1 < D ∧ D ≤ t.2.2.2.1 + t.2.2.2.2.1) ∨
    (u.2=7 ∧ t.2.2.2.1 + t.2.2.2.2.1 < D ∧ D ≤ t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1) ∨
    (u.2=11 ∧ t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 < D ∧
      D ≤ t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 + t.2.2.2.2.2.2) := by
  decide +kernel

/-- Every calibration prime is obtained through exact head cancellation. -/
theorem checkpoints_uncovered_from_head : ∀ t ∈ rootData,
    (paritySafeUncoveredCandidates t.1).Nonempty := by
  intro t ht
  obtain ⟨_,_,ha,hb⟩ := caps_checked t ht
  obtain ⟨_,_,_,hhead⟩ := head_charges_checked t ht
  apply uncovered_nonempty_of_remainingCap_lt (P := 11)
  rw [canonicalRemainingCap,hhead,ha,hb]
  have H : ∀ u ∈ rootData,
      u.2.2.1 - (u.2.2.2.1 + u.2.2.2.2.1 + u.2.2.2.2.2.1 + u.2.2.2.2.2.2) < u.2.1 := by decide +kernel
  exact H t ht

/-- Independent direct rough-currency prime proofs; no head or full E/I evaluation enters. -/
theorem checkpoints_prime_from_rough : ∀ t ∈ roughData, ∃ p, p.Prime ∧ SquareCell t.1 p := by
  intro t ht
  obtain ⟨hn,hlarge,hR,hI,hgap⟩ := rough_floor_counts_checked t ht
  apply prime_squareCell_of_roughEleven_count hn hlarge
  rwa [hR,hI]

theorem shell1009_uncovered : (paritySafeUncoveredCandidates 1009).Nonempty :=
  checkpoints_uncovered_from_head (1009,1008,1702,460,148,76,27) (by decide)

theorem shell1013_uncovered : (paritySafeUncoveredCandidates 1013).Nonempty :=
  checkpoints_uncovered_from_head (1013,1012,1721,461,159,79,49) (by decide)

theorem shell1009_prime : ∃ p, p.Prime ∧ SquareCell 1009 p :=
  checkpoints_prime_from_rough (1009,419,402) (by decide)

theorem shell1013_prime : ∃ p, p.Prime ∧ SquareCell 1013 p :=
  checkpoints_prime_from_rough (1013,421,382) (by decide)

end DkMathTest.LegendreCanonicalTailCalibration
