/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge
import DkMathTest.NumberTheory.LegendreHybridProvider

#print "file: DkMathTest.NumberTheory.LegendreCanonicalRootCharge"

namespace DkMathTest.LegendreCanonicalRootCharge
open DkMath.NumberTheory.Legendre
open DkMathTest.LegendreIncidenceUpper DkMathTest.LegendreHybridProvider
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators

set_option maxRecDepth 100000
-- Seven-field finite diagnostic rows need a larger instance-search expression budget.
set_option synthInstance.maxSize 1024

abbrev RootRow := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- (anchor, candidates, upper cap, root3, root5, root7, least successful root). -/
def rootData : Finset RootRow :=
  {((47,46,54,12,4,4,3) : RootRow), ((97,96,125,29,10,7,5) : RootRow), ((127,126,170,42,11,5,5) : RootRow),
   ((211,210,307,78,27,15,5) : RootRow), ((503,502,813,222,78,36,7) : RootRow)}

set_option maxHeartbeats 4000000 in
-- Evaluate only the structural floor differences at all active secondary primes.
theorem root_charges_checked : ∀ t ∈ rootData,
    canonicalRootCharge3 t.1 = t.2.2.2.1 ∧
    canonicalRootCharge5 t.1 = t.2.2.2.2.1 ∧
    canonicalRootCharge7 t.1 = t.2.2.2.2.2.1 := by
  simp_rw [canonicalRootCharge3, canonicalRootCharge5, canonicalRootCharge7,
    oddActive_eq_filter_range]
  decide +kernel

set_option maxHeartbeats 6000000 in
-- The cap and candidate count use their existing finite normal forms, not E or I.
theorem caps_checked : ∀ t ∈ rootData,
    t.1.Prime ∧ 7 < t.1 ∧
    (squareAnchorOddPointCoprimeOffsets t.1).card = t.2.1 ∧
    paritySafeTwoPrimeIncidenceUpper t.1 = t.2.2.1 := by
  simp_rw [candidate_eq_filter_Icc, twoPrimeUpper_eq_finite]
  decide +kernel

/-- Kernel-checked minimal cutoffs among initial active roots3,5,7. -/
theorem cutoff_checked : ∀ t ∈ rootData,
    let D := t.2.2.1 - t.2.1 + 1
    (t.2.2.2.2.2.2 = 3 ∧ D ≤ t.2.2.2.1) ∨
    (t.2.2.2.2.2.2 = 5 ∧ t.2.2.2.1 < D ∧ D ≤ t.2.2.2.1 + t.2.2.2.2.1) ∨
    (t.2.2.2.2.2.2 = 7 ∧ t.2.2.2.1 + t.2.2.2.2.1 < D ∧
      D ≤ t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1) := by
  decide +kernel

/-- Structural root charges, transported through the generic disjoint-root theorem. -/
theorem charges_le_excess : ∀ t ∈ rootData,
    t.2.2.2.1 ≤ paritySafeSupportExcess t.1 ∧
    t.2.2.2.1 + t.2.2.2.2.1 ≤ paritySafeSupportExcess t.1 ∧
    t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 ≤ paritySafeSupportExcess t.1 := by
  intro t ht
  obtain ⟨hn, hlarge, _, _⟩ := caps_checked t ht
  obtain ⟨h3, h5, h7⟩ := root_charges_checked t ht
  simpa only [h3, h5, h7] using canonicalSmallRootCharges_le_excess hn hlarge

/-- These root equalities are diagnostics and are not used by the demand proof. -/
theorem actual_root_fibers_checked : ∀ t ∈ rootData,
    (canonicalRootFiber t.1 3).card = t.2.2.2.1 ∧
    (canonicalRootFiber t.1 5).card = t.2.2.2.2.1 ∧
    (canonicalRootFiber t.1 7).card = t.2.2.2.2.2.1 := by
  intro t ht
  obtain ⟨hn, hlarge, _, _⟩ := caps_checked t ht
  obtain ⟨h3, h5, h7⟩ := root_charges_checked t ht
  obtain ⟨he3, he5, he7⟩ := canonicalSmallRootCharges_eq_fibers hn hlarge
  exact ⟨he3.symm.trans h3, he5.symm.trans h5, he7.symm.trans h7⟩

/-- The two hard demand values follow only from the checked structural caps. -/
theorem hard_demands_checked :
    paritySafeTwoPrimeIncidenceUpper 211 - (squareAnchorOddPointCoprimeOffsets 211).card + 1 = 98 ∧
    paritySafeTwoPrimeIncidenceUpper 503 - (squareAnchorOddPointCoprimeOffsets 503).card + 1 = 312 := by
  have h211 := caps_checked (211,210,307,78,27,15,5) (by decide)
  have h503 := caps_checked (503,502,813,222,78,36,7) (by decide)
  rw [h211.2.2.1, h211.2.2.2, h503.2.2.1, h503.2.2.2]
  decide

/-- 211 is solved by roots3 and5; its excess is never evaluated. -/
theorem shell211_uncovered : (paritySafeUncoveredCandidates 211).Nonempty := by
  have ht : ((211,210,307,78,27,15,5) : RootRow) ∈ rootData := by decide
  have hc := caps_checked _ ht
  have he := (charges_le_excess _ ht).2.1
  apply paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess he
  rw [hc.2.2.1, hc.2.2.2]
  decide

/-- 503 is solved by roots3,5,7; its excess is never evaluated. -/
theorem shell503_uncovered : (paritySafeUncoveredCandidates 503).Nonempty := by
  have ht : ((503,502,813,222,78,36,7) : RootRow) ∈ rootData := by decide
  have hc := caps_checked _ ht
  have he := (charges_le_excess _ ht).2.2
  apply paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess he
  rw [hc.2.2.1, hc.2.2.2]
  decide

theorem shell211_prime : ∃ p, p.Prime ∧ SquareCell 211 p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty (by decide) shell211_uncovered

theorem shell503_prime : ∃ p, p.Prime ∧ SquareCell 503 p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty (by decide) shell503_uncovered

end DkMathTest.LegendreCanonicalRootCharge
