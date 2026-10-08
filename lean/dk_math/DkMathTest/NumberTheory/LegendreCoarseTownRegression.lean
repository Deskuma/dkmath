/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarsePrimorialTown

#print "file: DkMathTest.NumberTheory.LegendreCoarseTownRegression"

namespace DkMathTest.LegendreCoarseTownRegression

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse
open DkMath.NumberTheory.StructuralArithmetic

private def computedSupport (n r : ℕ) : Finset ℕ :=
  (primeScalesUpTo n).filter (fun p => p ∣ n ^ 2 + r)

private theorem support_eq_computed (n r : ℕ) :
    squareOffsetPrimeSupport n r = computedSupport n r := by
  ext p
  simp [computedSupport, mem_squareOffsetPrimeSupport, and_assoc]

/-- The modulus-one exception stays explicit. -/
theorem modulus_one_boundary : primeWorldResidues ∅ ≠ squareAnchorCoprimeBaseOffsets 1 :=
  primeWorld_packet_modulus_one_mismatch.2.2.2

/-- An anchor phase changes which offsets survive, even within one period. -/
theorem phased_base_differs_from_offset_units :
    coarsePrimeWorldBase {2, 3} 4 = {1, 3} ∧
      squareAnchorCoprimeBaseOffsets 6 = {1, 5} ∧
      squareShellWheelProjection {2, 3} 4 3 = 1 ∧ 3 % 6 = 3 := by
  decide +kernel

/-- Same period and same address, despite an anchor not divisible by the modulus. -/
theorem nondivisor_anchor_coarse_pair :
    primeWorldModulus {2, 3} = 6 ∧ ¬ 6 ∣ 8 ∧
      1 ∈ coarsePrimeWorldBase {2, 3} 8 ∧
      Nat.Coprime (8 ^ 2 + 1) (8 ^ 2 + 7) ∧
      squareShellWheelProjection {2, 3} 8 1 = squareShellWheelProjection {2, 3} 8 7 := by
  decide +kernel

/-- Every pair is coprime, while two different packets reuse the old prime two. -/
theorem local_pairs_do_not_give_global_support_separation :
    coarsePrimeWorldTown {3} 3 = {1, 2, 4, 5} ∧
      Nat.Coprime 10 13 ∧ Nat.Coprime 11 14 ∧
      2 ∈ squareOffsetPrimeSupport 3 1 ∧ 2 ∈ squareOffsetPrimeSupport 3 5 := by
  rw [support_eq_computed, support_eq_computed]
  decide +kernel

theorem coarse_town_not_global_oldSupport_family :
    ¬ PairwiseOldSupportDisjointSquareSeatFamily 3 (coarsePrimeWorldTown {3} 3) := by
  intro h
  have hm : 1 ∈ coarsePrimeWorldTown {3} 3 ∧ 5 ∈ coarsePrimeWorldTown {3} 3 := by
    decide +kernel
  have hp : 2 ∈ squareOffsetPrimeSupport 3 1 ∧ 2 ∈ squareOffsetPrimeSupport 3 5 := by
    norm_num [mem_squareOffsetPrimeSupport]
  exact Finset.disjoint_left.mp (h.2 hm.1 hm.2 (by decide)) hp.1 hp.2

/-- Incidence is not packet cardinality. -/
theorem incidence_can_exceed_packet_count :
    (coarsePrimeWorldBase {3, 5} 42).card = 8 ∧ coarseCrossCount {3, 5} 42 = 10 := by
  unfold coarseCrossCount coarseCrossOffsets
  simp_rw [support_eq_computed]
  decide +kernel

/-- A near ordered pair really can hit more than one packet. -/
theorem near_pair_multiple_occupancy :
    ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p * q ≤ 105 ∧
      1 < (coarseCrossOffsets {3, 5, 7} 105 p q).card := by
  -- The witnesses are obtained from actual prime supports, not abstract assignments.
  refine ⟨2, 11, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold coarseCrossOffsets
  simp_rw [support_eq_computed]
  decide +kernel

/-- A finite actual-support certificate is passed directly to the existing consumer. -/
theorem six_oldSupport_family :
    PairwiseOldSupportDisjointSquareSeatFamily 6 {1, 5, 7, 11} := by
  have hseats : ∀ r ∈ ({1, 5, 7, 11} : Finset ℕ), SquareOffset 6 r := by
    norm_num [SquareOffset]
  have hs : ∀ r ∈ ({1, 5, 7, 11} : Finset ℕ), squareOffsetPrimeSupport 6 r = ∅ := by
    simp_rw [support_eq_computed]
    decide +kernel
  refine ⟨hseats, ?_⟩
  intro r hr s hs' hrs
  change Disjoint (squareOffsetPrimeSupport 6 r) (squareOffsetPrimeSupport 6 s)
  rw [hs r hr, hs s hs']
  exact Finset.disjoint_empty_left ∅

theorem six_prime_via_existing_capacity_consumer :
    ∃ p, p.Prime ∧ SquareCell 6 p := by
  apply exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    (by decide) six_oldSupport_family
  decide +kernel

theorem six_family_is_entire_coarse_town :
    coarsePrimeWorldTown {2, 3} 6 = {1, 5, 7, 11} := by
  decide +kernel

/-- The entire same-anchor odd-gap world is too large for these coarse streets. -/
theorem odd_gap_world_does_not_fit_three :
    centeredOddGapPrimeWorld 3 = {3, 5} ∧
      primeWorldModulus (centeredOddGapPrimeWorld 3) = 15 ∧ ¬ 15 ≤ 3 := by
  decide +kernel

end DkMathTest.LegendreCoarseTownRegression
