/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation

#print "file: DkMathTest.NumberTheory.LegendreConservationRegression"

namespace DkMathTest.LegendreConservationRegression

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem one_base_coordinates :
    (coarsePrimeWorldFullTown ∅ 1).card = 2 ∧
      (coarseOutsidePrimes ∅ 1).card = 0 ∧
      (coarseFullTownActivePrimes ∅ 1).card = 0 ∧
      (coarseFullTownUncoveredSeats ∅ 1).card = 2 ∧
      coarseFullTownIncidence ∅ 1 = 0 ∧
      (coarseTownDeletionVertices ∅ 1).card = 0 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseFullTownIncidence_eq_divisibility_sum,
    coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
    coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem one_conservation_coordinates :
    (coarseTownPackingRemainder ∅ 1).card = 2 ∧
      coarseFullTownSupportExcess ∅ 1 = 0 ∧
      coarseTownDeletionMass ∅ 1 = 0 ∧
      coarseTownDeletionOverlap ∅ 1 = 0 := by
  have hS : KnownPrimeScales (∅ : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  have hp := card_coarseTownDeletion_partition ∅ 1
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS 1
  have hm := coarseTownDeletionMass_add_active_eq_incidence ∅ 1
  have ho := card_deletion_add_overlap_eq_mass hS 1
  obtain ⟨hv,ht,ha,hu,hi,hd⟩ := one_base_coordinates
  omega

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
set_option linter.unnecessarySimpa false in
theorem one_master_checked : (2 : ℕ) + 0 = 2 + 0 + 0 := by
  have hS : KnownPrimeScales (∅ : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  simpa only [one_conservation_coordinates.1, one_conservation_coordinates.2.1,
    one_base_coordinates.2.2.2.1, one_base_coordinates.2.2.1,
    one_conservation_coordinates.2.2.2] using (coarseTown_remainder_conservation hS 1)

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem five_base_coordinates :
    (coarsePrimeWorldFullTown {2} 5).card = 5 ∧
      (coarseOutsidePrimes {2} 5).card = 2 ∧
      (coarseFullTownActivePrimes {2} 5).card = 2 ∧
      (coarseFullTownUncoveredSeats {2} 5).card = 2 ∧
      coarseFullTownIncidence {2} 5 = 3 ∧
      (coarseTownDeletionVertices {2} 5).card = 1 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseFullTownIncidence_eq_divisibility_sum,
    coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
    coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem five_conservation_coordinates :
    (coarseTownPackingRemainder {2} 5).card = 4 ∧
      coarseFullTownSupportExcess {2} 5 = 0 ∧
      coarseTownDeletionMass {2} 5 = 1 ∧
      coarseTownDeletionOverlap {2} 5 = 0 := by
  have hS : KnownPrimeScales ({2} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  have hp := card_coarseTownDeletion_partition {2} 5
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS 5
  have hm := coarseTownDeletionMass_add_active_eq_incidence {2} 5
  have ho := card_deletion_add_overlap_eq_mass hS 5
  obtain ⟨hv,ht,ha,hu,hi,hd⟩ := five_base_coordinates
  omega

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
set_option linter.unnecessarySimpa false in
theorem five_master_checked : (4 : ℕ) + 0 = 2 + 2 + 0 := by
  have hS : KnownPrimeScales ({2} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  simpa only [five_conservation_coordinates.1, five_conservation_coordinates.2.1,
    five_base_coordinates.2.2.2.1, five_base_coordinates.2.2.1,
    five_conservation_coordinates.2.2.2] using (coarseTown_remainder_conservation hS 5)

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem eleven_base_coordinates :
    (coarsePrimeWorldFullTown {2, 3} 11).card = 6 ∧
      (coarseOutsidePrimes {2, 3} 11).card = 3 ∧
      (coarseFullTownActivePrimes {2, 3} 11).card = 2 ∧
      (coarseFullTownUncoveredSeats {2, 3} 11).card = 4 ∧
      coarseFullTownIncidence {2, 3} 11 = 2 ∧
      (coarseTownDeletionVertices {2, 3} 11).card = 0 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseFullTownIncidence_eq_divisibility_sum,
    coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
    coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem eleven_conservation_coordinates :
    (coarseTownPackingRemainder {2, 3} 11).card = 6 ∧
      coarseFullTownSupportExcess {2, 3} 11 = 0 ∧
      coarseTownDeletionMass {2, 3} 11 = 0 ∧
      coarseTownDeletionOverlap {2, 3} 11 = 0 := by
  have hS : KnownPrimeScales ({2, 3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  have hp := card_coarseTownDeletion_partition {2, 3} 11
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS 11
  have hm := coarseTownDeletionMass_add_active_eq_incidence {2, 3} 11
  have ho := card_deletion_add_overlap_eq_mass hS 11
  obtain ⟨hv,ht,ha,hu,hi,hd⟩ := eleven_base_coordinates
  omega

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
set_option linter.unnecessarySimpa false in
theorem eleven_master_checked : (6 : ℕ) + 0 = 4 + 2 + 0 := by
  have hS : KnownPrimeScales ({2, 3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  simpa only [eleven_conservation_coordinates.1, eleven_conservation_coordinates.2.1,
    eleven_base_coordinates.2.2.2.1, eleven_base_coordinates.2.2.1,
    eleven_conservation_coordinates.2.2.2] using (coarseTown_remainder_conservation hS 11)

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem elevenOdd_base_coordinates :
    (coarsePrimeWorldFullTown {3} 11).card = 14 ∧
      (coarseOutsidePrimes {3} 11).card = 4 ∧
      (coarseFullTownActivePrimes {3} 11).card = 3 ∧
      (coarseFullTownUncoveredSeats {3} 11).card = 4 ∧
      coarseFullTownIncidence {3} 11 = 13 ∧
      (coarseTownDeletionVertices {3} 11).card = 9 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseFullTownIncidence_eq_divisibility_sum,
    coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
    coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem elevenOdd_conservation_coordinates :
    (coarseTownPackingRemainder {3} 11).card = 5 ∧
      coarseFullTownSupportExcess {3} 11 = 3 ∧
      coarseTownDeletionMass {3} 11 = 10 ∧
      coarseTownDeletionOverlap {3} 11 = 1 := by
  have hS : KnownPrimeScales ({3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  have hp := card_coarseTownDeletion_partition {3} 11
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS 11
  have hm := coarseTownDeletionMass_add_active_eq_incidence {3} 11
  have ho := card_deletion_add_overlap_eq_mass hS 11
  obtain ⟨hv,ht,ha,hu,hi,hd⟩ := elevenOdd_base_coordinates
  omega

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
set_option linter.unnecessarySimpa false in
theorem elevenOdd_master_checked : (5 : ℕ) + 3 = 4 + 3 + 1 := by
  have hS : KnownPrimeScales ({3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  simpa only [elevenOdd_conservation_coordinates.1, elevenOdd_conservation_coordinates.2.1,
    elevenOdd_base_coordinates.2.2.2.1, elevenOdd_base_coordinates.2.2.1,
    elevenOdd_conservation_coordinates.2.2.2] using (coarseTown_remainder_conservation hS 11)

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem nineteen_base_coordinates :
    (coarsePrimeWorldFullTown {2, 3} 19).card = 12 ∧
      (coarseOutsidePrimes {2, 3} 19).card = 6 ∧
      (coarseFullTownActivePrimes {2, 3} 19).card = 5 ∧
      (coarseFullTownUncoveredSeats {2, 3} 19).card = 6 ∧
      coarseFullTownIncidence {2, 3} 19 = 8 ∧
      (coarseTownDeletionVertices {2, 3} 19).card = 3 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseFullTownIncidence_eq_divisibility_sum,
    coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
    coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem nineteen_conservation_coordinates :
    (coarseTownPackingRemainder {2, 3} 19).card = 9 ∧
      coarseFullTownSupportExcess {2, 3} 19 = 2 ∧
      coarseTownDeletionMass {2, 3} 19 = 3 ∧
      coarseTownDeletionOverlap {2, 3} 19 = 0 := by
  have hS : KnownPrimeScales ({2, 3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  have hp := card_coarseTownDeletion_partition {2, 3} 19
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS 19
  have hm := coarseTownDeletionMass_add_active_eq_incidence {2, 3} 19
  have ho := card_deletion_add_overlap_eq_mass hS 19
  obtain ⟨hv,ht,ha,hu,hi,hd⟩ := nineteen_base_coordinates
  omega

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
set_option linter.unnecessarySimpa false in
theorem nineteen_master_checked : (9 : ℕ) + 2 = 6 + 5 + 0 := by
  have hS : KnownPrimeScales ({2, 3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  simpa only [nineteen_conservation_coordinates.1, nineteen_conservation_coordinates.2.1,
    nineteen_base_coordinates.2.2.2.1, nineteen_base_coordinates.2.2.1,
    nineteen_conservation_coordinates.2.2.2] using (coarseTown_remainder_conservation hS 19)

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem twentynine_base_coordinates :
    (coarsePrimeWorldFullTown {2, 3} 29).card = 18 ∧
      (coarseOutsidePrimes {2, 3} 29).card = 8 ∧
      (coarseFullTownActivePrimes {2, 3} 29).card = 6 ∧
      (coarseFullTownUncoveredSeats {2, 3} 29).card = 8 ∧
      coarseFullTownIncidence {2, 3} 29 = 13 ∧
      (coarseTownDeletionVertices {2, 3} 29).card = 4 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseFullTownIncidence_eq_divisibility_sum,
    coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
    coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem twentynine_conservation_coordinates :
    (coarseTownPackingRemainder {2, 3} 29).card = 14 ∧
      coarseFullTownSupportExcess {2, 3} 29 = 3 ∧
      coarseTownDeletionMass {2, 3} 29 = 7 ∧
      coarseTownDeletionOverlap {2, 3} 29 = 3 := by
  have hS : KnownPrimeScales ({2, 3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  have hp := card_coarseTownDeletion_partition {2, 3} 29
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS 29
  have hm := coarseTownDeletionMass_add_active_eq_incidence {2, 3} 29
  have ho := card_deletion_add_overlap_eq_mass hS 29
  obtain ⟨hv,ht,ha,hu,hi,hd⟩ := twentynine_base_coordinates
  omega

set_option maxHeartbeats 2000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
set_option linter.unnecessarySimpa false in
theorem twentynine_master_checked : (14 : ℕ) + 3 = 8 + 6 + 3 := by
  have hS : KnownPrimeScales ({2, 3} : Finset ℕ) := by unfold KnownPrimeScales; decide +kernel
  simpa only [twentynine_conservation_coordinates.1, twentynine_conservation_coordinates.2.1,
    twentynine_base_coordinates.2.2.2.1, twentynine_base_coordinates.2.2.1,
    twentynine_conservation_coordinates.2.2.2] using (coarseTown_remainder_conservation hS 29)

/-- Smallest positive anchor refutes the uncovered-free equivalence. -/
theorem smallest_false_equivalence :
    (coarseOutsidePrimes ∅ 1).card + (coarseTownDeletionVertices ∅ 1).card <
      (coarsePrimeWorldFullTown ∅ 1).card ∧
    ¬ (coarseOutsidePrimes ∅ 1).card + coarseFullTownSupportExcess ∅ 1 <
      (coarseFullTownActivePrimes ∅ 1).card + coarseTownDeletionOverlap ∅ 1 := by
  obtain ⟨hv,ht,ha,_hu,_hi,hd⟩ := one_base_coordinates
  obtain ⟨_hr,hx,_hm,ho⟩ := one_conservation_coordinates
  omega

/-- A nonempty active universe already exhibits the same strictness at n=5. -/
theorem five_false_equivalence :
    (coarseOutsidePrimes {2} 5).card + (coarseTownDeletionVertices {2} 5).card <
      (coarsePrimeWorldFullTown {2} 5).card ∧
    ¬ (coarseOutsidePrimes {2} 5).card + coarseFullTownSupportExcess {2} 5 <
      (coarseFullTownActivePrimes {2} 5).card + coarseTownDeletionOverlap {2} 5 := by
  obtain ⟨hv,ht,ha,_hu,_hi,hd⟩ := five_base_coordinates
  obtain ⟨_hr,hx,_hm,ho⟩ := five_conservation_coordinates
  omega

end DkMathTest.LegendreConservationRegression
