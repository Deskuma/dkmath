/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation

#print "file: DkMathTest.NumberTheory.LegendreSurvivor297Calibration"

namespace DkMathTest.LegendreSurvivor297Calibration

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

set_option maxRecDepth 100000

/-- Arithmetic carriers checked against production, not external theorem premises. -/
def town297Seats : Finset ℕ := ([2, 4, 8, 10, 14, 20, 22, 28, 32, 34, 38, 44, 50, 52, 58, 62, 64, 70, 74, 80, 88, 92, 94, 98, 100, 104, 112, 118, 122, 128, 130, 134, 140, 142, 148, 154, 158, 160, 164, 170, 172, 178, 182, 184, 188, 190, 200, 202, 212, 214, 218, 220, 224, 230, 232, 238, 242, 244, 248, 254, 260, 262, 268, 272, 274, 280, 284, 290, 298, 302, 304, 308, 310, 314, 322, 328, 332, 338, 340, 344, 350, 352, 358, 364, 368, 370, 374, 380, 382, 388, 392, 394, 398, 400, 410, 412] : List ℕ).toFinset

def oldPrimes297 : Finset ℕ := ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293] : List ℕ).toFinset

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem town297Seats_eq_production :
    coarsePrimeWorldFullTown (primeScalesUpTo 10) 297 = town297Seats := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem oldPrimes297_eq_production : primeScalesUpTo 297 = oldPrimes297 := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem geometry297_checked :
    primeWorldModulus (primeScalesUpTo 10) = 210 ∧
      coarsePrimeWorldPeriodCount (primeScalesUpTo 10) 297 = 2 ∧
      (coarsePrimeWorldFullTown (primeScalesUpTo 10) 297).card = 96 ∧
      (coarseOutsidePrimes (primeScalesUpTo 10) 297).card = 58 ∧
      (primeScalesUpTo 297).card = 62 := by
  rw [town297Seats_eq_production]
  unfold coarseOutsidePrimes
  rw [oldPrimes297_eq_production]
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem deletion297_cards_checked :
    (coarseTownDeletionVertices (primeScalesUpTo 10) 297).card = 39 ∧
      (coarseTownRightDeletionVertices (primeScalesUpTo 10) 297).card = 36 := by
  rw [coarseTownDeletionVertices_eq_fibers, coarseTownRightDeletionVertices_eq_fibers]
  unfold coarseTownDeletionByFibers coarseTownRightDeletionByFibers
    coarseTownDivisibilityFiber oldSupportSeatFiber
  rw [town297Seats_eq_production, oldPrimes297_eq_production]
  decide +kernel

theorem remainder297_cards :
    (coarseTownPackingRemainder (primeScalesUpTo 10) 297).card = 57 ∧
      (coarseTownRightPackingRemainder (primeScalesUpTo 10) 297).card = 60 := by
  have hp := card_coarseTownDeletion_partition (primeScalesUpTo 10) 297
  have hr := card_coarseTownRightDeletion_partition (primeScalesUpTo 10) 297
  have hv := geometry297_checked.2.2.1
  obtain ⟨hl,hd⟩ := deletion297_cards_checked
  omega

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
/-- Strict improvement over the old-world capacity, using the identical right selector. -/
theorem survivor297_right_strictness :
    (coarseOutsidePrimes (primeScalesUpTo 10) 297).card <
      (coarseTownRightPackingRemainder (primeScalesUpTo 10) 297).card ∧
    ¬ (primeScalesUpTo 297).card <
      (coarseTownRightPackingRemainder (primeScalesUpTo 10) 297).card := by
  rw [geometry297_checked.2.2.2.1, geometry297_checked.2.2.2.2, remainder297_cards.2]
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
/-- Production right deletion and outside-world capacity, with no 63-seat certificate import. -/
theorem exists_prime_squareCell_297_of_right_survivor_deletion :
    ∃ p, p.Prime ∧ SquareCell 297 p := by
  apply exists_prime_squareCell_of_coarseTown_outside_right_deletion_deficit
    (knownPrimeScales_primeScalesUpTo 10) (by decide)
  rw [geometry297_checked.2.2.2.1, deletion297_cards_checked.2, geometry297_checked.2.2.1]
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem incidence297_checked : coarseFullTownIncidence (primeScalesUpTo 10) 297 = 88 := by
  rw [coarseFullTownIncidence_eq_divisibility_sum]
  unfold coarseTownDivisibilityFiber oldSupportSeatFiber coarseOutsidePrimes
  rw [town297Seats_eq_production, oldPrimes297_eq_production]
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem active297_checked : (coarseFullTownActivePrimes (primeScalesUpTo 10) 297).card = 40 := by
  rw [coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDivisibilityFiber oldSupportSeatFiber coarseOutsidePrimes
  rw [town297Seats_eq_production, oldPrimes297_eq_production]
  decide +kernel

set_option maxHeartbeats 10000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem uncovered297_checked : (coarseFullTownUncoveredSeats (primeScalesUpTo 10) 297).card = 29 := by
  unfold coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  unfold boundedSquareSupport
  rw [town297Seats_eq_production, oldPrimes297_eq_production]
  decide +kernel

theorem conservation297_coordinates :
    coarseFullTownSupportExcess (primeScalesUpTo 10) 297 = 21 ∧
      coarseTownDeletionMass (primeScalesUpTo 10) 297 = 48 ∧
      coarseTownDeletionOverlap (primeScalesUpTo 10) 297 = 9 := by
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess
    (knownPrimeScales_primeScalesUpTo 10) 297
  have hm := coarseTownDeletionMass_add_active_eq_incidence (primeScalesUpTo 10) 297
  have ho := card_deletion_add_overlap_eq_mass (knownPrimeScales_primeScalesUpTo 10) 297
  rw [incidence297_checked, uncovered297_checked, geometry297_checked.2.2.1] at hs
  rw [active297_checked, incidence297_checked] at hm
  rw [deletion297_cards_checked.1] at ho
  omega

set_option linter.unnecessarySimpa false in
/-- Numeric normalization of the production master identity: 57+21=29+40+9. -/
theorem master297_checked : (57 : ℕ) + 21 = 29 + 40 + 9 := by
  simpa only [remainder297_cards.1, conservation297_coordinates.1, uncovered297_checked,
    active297_checked, conservation297_coordinates.2.2] using
    (coarseTown_remainder_conservation (knownPrimeScales_primeScalesUpTo 10) 297)

end DkMathTest.LegendreSurvivor297Calibration
