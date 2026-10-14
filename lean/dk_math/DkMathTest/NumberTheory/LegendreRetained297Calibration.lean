/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSymmetricDeletion
import DkMathTest.NumberTheory.LegendreSurvivor297Calibration

#print "file: DkMathTest.NumberTheory.LegendreRetained297Calibration"

namespace DkMathTest.LegendreRetained297Calibration

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic DkMath.Combinatorics
open DkMathTest.LegendreSurvivor297Calibration

set_option maxRecDepth 100000

private def leftSeats : Finset ℕ := ([2, 14, 28, 32, 50, 52, 80, 92, 94, 98, 104, 112, 118, 128, 130, 148, 170, 182, 188, 190, 200, 202, 214, 218, 224, 238, 244, 248, 254, 260, 262, 268, 280, 284, 290, 298, 302, 304, 314, 322, 328, 332, 338, 340, 358, 368, 370, 374, 380, 382, 388, 392, 394, 398, 400, 410, 412] : List ℕ).toFinset

set_option maxHeartbeats 30000000 in
-- Check the entire arithmetic remainder carrier, not only its card.
theorem left_carrier_checked : coarseTownPackingRemainder (primeScalesUpTo 10) 297 = leftSeats := by
  change coarsePrimeWorldFullTown (primeScalesUpTo 10) 297 \ coarseTownDeletionVertices (primeScalesUpTo 10) 297 = _
  rw [coarseTownDeletionVertices_eq_fibers]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
  rw [town297Seats_eq_production,oldPrimes297_eq_production]
  decide +kernel

set_option maxHeartbeats 30000000 in
-- Actual supports are recomputed from divisibility over a kernel-certified carrier.
theorem left_represented_checked : (coarseTownRepresentedPrimes (primeScalesUpTo 10) 297).card = 31 := by
  unfold coarseTownRepresentedPrimes representedDirections
  rw [left_carrier_checked]
  rw [show squareOffsetPrimeSupport 297 = boundedSquareSupport 297 from
    funext (squareOffsetPrimeSupport_eq_boundedSquareSupport 297)]
  unfold boundedSquareSupport
  rw [oldPrimes297_eq_production]
  decide +kernel

private def rightSeats : Finset ℕ := ([2, 4, 8, 10, 14, 20, 22, 28, 32, 34, 50, 52, 58, 62, 64, 70, 80, 92, 94, 98, 112, 118, 128, 130, 142, 148, 158, 164, 170, 172, 182, 184, 188, 190, 200, 202, 214, 218, 224, 232, 238, 244, 254, 260, 262, 280, 284, 290, 304, 314, 322, 338, 340, 368, 370, 380, 382, 394, 398, 400] : List ℕ).toFinset

set_option maxHeartbeats 30000000 in
-- Check the entire arithmetic remainder carrier, not only its card.
theorem right_carrier_checked : coarseTownRightPackingRemainder (primeScalesUpTo 10) 297 = rightSeats := by
  change coarsePrimeWorldFullTown (primeScalesUpTo 10) 297 \ coarseTownRightDeletionVertices (primeScalesUpTo 10) 297 = _
  rw [coarseTownRightDeletionVertices_eq_fibers]
  unfold coarseTownRightDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
  rw [town297Seats_eq_production,oldPrimes297_eq_production]
  decide +kernel

set_option maxHeartbeats 30000000 in
-- Actual supports are recomputed from divisibility over a kernel-certified carrier.
theorem right_represented_checked : (coarseTownRightRepresentedPrimes (primeScalesUpTo 10) 297).card = 32 := by
  unfold coarseTownRightRepresentedPrimes representedDirections
  rw [right_carrier_checked]
  rw [show squareOffsetPrimeSupport 297 = boundedSquareSupport 297 from
    funext (squareOffsetPrimeSupport_eq_boundedSquareSupport 297)]
  unfold boundedSquareSupport
  rw [oldPrimes297_eq_production]
  decide +kernel

open DkMathTest.LegendreSurvivor297Calibration

theorem left_loss_decomposition_checked :
    coarseTownSupportLoss (primeScalesUpTo 10) 297 = 12 ∧
      (coarseTownUnrepresentedActivePrimes (primeScalesUpTo 10) 297).card = 9 ∧
      coarseTownRetainedSupportExcess (primeScalesUpTo 10) 297 = 3 := by
  have hS := knownPrimeScales_primeScalesUpTo 10
  have hl := coarseTown_remainder_add_loss_eq_uncovered_add_active hS 297
  have hd := coarseTown_loss_decomposition hS 297
  have hp := coarseTown_active_card_partition hS 297
  rw [remainder297_cards.1,uncovered297_checked,active297_checked] at hl
  rw [left_represented_checked,active297_checked] at hp
  omega

theorem right_loss_decomposition_checked :
    coarseTownRightSupportLoss (primeScalesUpTo 10) 297 = 9 ∧
      (coarseTownRightUnrepresentedActivePrimes (primeScalesUpTo 10) 297).card = 8 ∧
      coarseTownRightRetainedSupportExcess (primeScalesUpTo 10) 297 = 1 := by
  have hS := knownPrimeScales_primeScalesUpTo 10
  have hl := coarseTownRight_remainder_add_loss hS 297
  have hd := coarseTownRight_loss_decomposition hS 297
  have hp := coarseTownRight_active_card_partition hS 297
  rw [remainder297_cards.2,uncovered297_checked,active297_checked] at hl
  rw [right_represented_checked,active297_checked] at hp
  omega

theorem better_orientation_checked :
    coarseTownBetterRemainder (primeScalesUpTo 10) 297 =
      coarseTownRightPackingRemainder (primeScalesUpTo 10) 297 := by
  unfold coarseTownBetterRemainder
  rw [remainder297_cards.1,remainder297_cards.2]
  rfl

theorem better_cards_checked :
    (coarseTownBetterRemainder (primeScalesUpTo 10) 297).card = 60 ∧
      coarseTownBetterLoss (primeScalesUpTo 10) 297 = 9 := by
  rw [card_coarseTownBetterRemainder]
  unfold coarseTownBetterLoss
  rw [remainder297_cards.1,remainder297_cards.2,
    left_loss_decomposition_checked.1,right_loss_decomposition_checked.1]
  decide +kernel

theorem exists_prime_squareCell_297_of_better_selector : ∃ p, p.Prime ∧ SquareCell 297 p := by
  apply exists_prime_squareCell_of_coarseTownBetter_deficit (knownPrimeScales_primeScalesUpTo 10) (by decide)
  rw [geometry297_checked.2.2.2.1,better_cards_checked.1]
  decide +kernel

end DkMathTest.LegendreRetained297Calibration
