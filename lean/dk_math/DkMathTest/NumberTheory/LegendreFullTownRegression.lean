/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSupportPacking
import DkMathTest.NumberTheory.LegendreCoarseTownRegression

#print "file: DkMathTest.NumberTheory.LegendreFullTownRegression"

namespace DkMathTest.LegendreFullTownRegression

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

private def computedSupport (n r : ℕ) : Finset ℕ :=
  (primeScalesUpTo n).filter (fun p => p ∣ n ^ 2 + r)

private theorem support_eq_computed (n r : ℕ) :
    squareOffsetPrimeSupport n r = computedSupport n r := by
  ext p
  simp [computedSupport, mem_squareOffsetPrimeSupport, and_assoc]

/-- A generic uncertified zero modulus gives no complete-period seats. -/
theorem zero_modulus_boundary :
    primeWorldModulus {0} = 0 ∧ coarsePrimeWorldPeriodCount {0} 5 = 0 ∧
      coarsePrimeWorldFullTown {0} 5 = ∅ := by
  decide +kernel

/-- The endpoint representative r=M participates in the empty-world grid. -/
theorem modulus_one_endpoint :
    coarsePrimeWorldBase ∅ 3 = {1} ∧ coarsePrimeWorldFullTown ∅ 3 = {1, 2, 3, 4, 5, 6} := by
  decide +kernel

theorem period_two_recovers_previous_town :
    coarsePrimeWorldFullTown {2, 3} 8 = coarsePrimeWorldTown {2, 3} 8 :=
  coarseFullTown_eq_twoStreet_of_periodCount_two (by decide +kernel)

/-- The old n=3 support-reuse obstruction persists in the full grid. -/
theorem three_fullTown_not_global_family :
    ¬ PairwiseOldSupportDisjointSquareSeatFamily 3 (coarsePrimeWorldFullTown {3} 3) := by
  rw [coarseFullTown_eq_twoStreet_of_periodCount_two (by decide +kernel)]
  exact DkMathTest.LegendreCoarseTownRegression.coarse_town_not_global_oldSupport_family

/-- Even uniformly sparse columns do not make the whole town a disjoint family. -/
theorem three_uniform_columns_not_global :
    (∀ q ∈ coarseOutsidePrimes {3} 3, coarsePrimeWorldPeriodCount {3} 3 ≤ q) ∧
      ¬ PairwiseOldSupportDisjointSquareSeatFamily 3 (coarsePrimeWorldFullTown {3} 3) :=
  ⟨by decide +kernel, three_fullTown_not_global_family⟩

/-- A five-street column can reuse q=3: uniform sparsity is a real hypothesis. -/
theorem five_vertical_reuse :
    coarsePrimeWorldPeriodCount {2} 5 = 5 ∧
      3 ∣ 5 ^ 2 + 2 ∧ 3 ∣ 5 ^ 2 + 2 + 3 * primeWorldModulus {2} ∧
      (coarseColumnWaveIndices {2} 5 2 3).card = 2 := by
  decide +kernel

/-- The older necessary assignment bound passes; the new capacity bound fails. -/
theorem five_strictly_improves_twoStreet :
    Nat.totient (primeWorldModulus {2}) ≤
      (∑ pq ∈ coarseNearPairs {2} 5, (coarseCrossOffsets {2} 5 pq.1 pq.2).card) +
        (coarseFarPairs {2} 5).card ∧
      coarseVerticalCapacity {2} 5 = 3 ∧ coarsePrimeWorldPeriodCount {2} 5 = 5 := by
  unfold coarseCrossOffsets
  simp_rw [support_eq_computed]
  decide +kernel

/-- Every strict vertical deficit discovered in the scan has a bounded kernel certificate. -/
def verticalDeficitCalibrations : Finset (ℕ × Finset ℕ) :=
  {(1, ∅), (2, {2}), (2, ∅), (3, {2}), (3, {3}), (4, {2}), (4, {3}),
    (5, {2}), (6, {2, 3}), (6, {3}), (9, {2, 3}), (10, {2, 3}),
    (12, {2, 3}), (15, {2, 3}), (16, {2, 3})}

theorem verticalDeficitCalibrations_certified :
    ∀ c ∈ verticalDeficitCalibrations, 0 < c.1 ∧ KnownPrimeScales c.2 ∧
      coarseVerticalCapacity c.2 c.1 < coarsePrimeWorldPeriodCount c.2 c.1 := by
  unfold KnownPrimeScales
  decide +kernel

/-- The finite list is consumed by Frontier, without testing the primality of a chosen witness. -/
theorem calibrated_vertical_prime_endpoints {n : ℕ} {S : Finset ℕ}
    (hc : (n, S) ∈ verticalDeficitCalibrations) : ∃ p, p.Prime ∧ SquareCell n p := by
  obtain ⟨hn, hS, hdef⟩ := verticalDeficitCalibrations_certified (n, S) hc
  exact exists_prime_squareCell_of_coarseVerticalCapacity_deficit hS hn hdef

theorem five_prime_via_vertical_consumer : ∃ p, p.Prime ∧ SquareCell 5 p :=
  calibrated_vertical_prime_endpoints (by decide +kernel : (5, {2}) ∈ verticalDeficitCalibrations)

/-- The edge route is strict at eleven even when the vertical bound has equality. -/
theorem eleven_edge_geometry :
    coarseVerticalCapacity {2, 3} 11 = coarsePrimeWorldPeriodCount {2, 3} 11 ∧
      (coarsePrimeWorldFullTown {2, 3} 11).card = 6 ∧ (primeScalesUpTo 11).card = 5 ∧
      coarseTownSupportCollisionEdges {2, 3} 11 = ∅ := by
  unfold coarseTownSupportCollisionEdges DkMath.Combinatorics.supportCollisionEdges
  simp_rw [support_eq_computed]
  decide +kernel

theorem eleven_prime_via_existing_packing_consumer : ∃ p, p.Prime ∧ SquareCell 11 p := by
  apply exists_prime_squareCell_of_coarseTown_edge_deficit {2, 3} (by decide)
  rw [eleven_edge_geometry.2.1, eleven_edge_geometry.2.2.1, eleven_edge_geometry.2.2.2]
  decide +kernel

/-- A common two-prime edge is counted twice by the prime-fiber sum. -/
theorem eleven_multiPrime_edge_overcount :
    (coarseTownSupportCollisionEdges {3} 11).card = 31 ∧
      (∑ q ∈ coarseOutsidePrimes {3} 11, (coarseFullTownPrimeFiber {3} 11 q).card.choose 2) = 32 := by
  unfold coarseTownSupportCollisionEdges DkMath.Combinatorics.supportCollisionEdges
    coarseFullTownPrimeFiber
  simp_rw [support_eq_computed]
  decide +kernel

/-- Canonical refinement really includes the square-anchor block shift. -/
theorem five_refinement_phase :
    (5 ^ 2 + 2) % primeWorldModulus {2} = 1 ∧
      (5 ^ 2 + 2) / primeWorldModulus {2} = 13 ∧
      primeWorldChild {2} 1 3 + 13 * primeWorldModulus {2} = 5 ^ 2 + 2 + 3 * primeWorldModulus {2} := by
  decide +kernel

/-- The operational 1031 initial world has nine streets and 432 complete-period seats. -/
theorem large_anchor_grid :
    primeScalesUpTo 10 = ({2, 3, 5, 7} : Finset ℕ) ∧
      coarsePrimeWorldPeriodCount (primeScalesUpTo 10) 1031 = 9 ∧
      (coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031).card = 432 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [card_coarsePrimeWorldFullTown (knownPrimeScales_primeScalesUpTo 10) 1031]
  decide +kernel

/-- Every full column at 1031 meets the production family API. -/
theorem large_anchor_column_family {r : ℕ}
    (hr : r ∈ coarsePrimeWorldBase (primeScalesUpTo 10) 1031) :
    PairwiseOldSupportDisjointSquareSeatFamily 1031
      (coarsePrimeWorldColumn (primeScalesUpTo 10) 1031 r) := by
  apply coarseColumn_oldSupport_family_initial hr
  decide +kernel

end DkMathTest.LegendreFullTownRegression
