/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSymmetricDeletion
import DkMathTest.NumberTheory.LegendreSurvivor1031Calibration
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

#print "file: DkMathTest.NumberTheory.LegendreRetained1031Calibration"

namespace DkMathTest.LegendreRetained1031Calibration

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic DkMath.Combinatorics
open DkMathTest.LegendreSurvivor1031Calibration
open DkMathTest.LegendreDeletion1031Data DkMathTest.LegendreDeletion1031Calibration

set_option maxRecDepth 100000

private def leftList : List ℕ := [6, 16, 18, 28, 40, 48, 58, 72, 78, 82, 96, 106, 118, 126, 130, 148, 162, 190, 196, 198, 216, 228, 232, 240, 252, 258, 280, 282, 312, 316, 340, 342, 358, 390, 408, 418, 436, 438, 448, 460, 462, 466, 480, 492, 496, 502, 510, 516, 520, 522, 540, 562, 568, 580, 586, 588, 592, 600, 606, 622, 630, 636, 646, 648, 652, 658, 666, 676, 688, 700, 732, 736, 748, 756, 760, 768, 778, 786, 796, 810, 820, 840, 852, 862, 870, 876, 880, 886, 888, 898, 910, 912, 922, 930, 936, 942, 952, 958, 960, 966, 1000, 1002, 1006, 1008, 1012, 1026, 1038, 1056, 1068, 1098, 1108, 1110, 1126, 1140, 1150, 1152, 1156, 1162, 1170, 1192, 1198, 1216, 1218, 1230, 1236, 1240, 1266, 1282, 1288, 1296, 1302, 1308, 1320, 1330, 1350, 1356, 1360, 1372, 1378, 1380, 1390, 1398, 1402, 1408, 1416, 1420, 1422, 1446, 1450, 1462, 1470, 1482, 1488, 1500, 1506, 1510, 1512, 1516, 1530, 1540, 1546, 1558, 1560, 1566, 1572, 1582, 1588, 1612, 1618, 1626, 1632, 1636, 1638, 1656, 1660, 1668, 1672, 1678, 1692, 1702, 1708, 1710, 1720, 1722, 1728, 1738, 1750, 1756, 1758, 1768, 1770, 1776, 1782, 1786, 1792, 1798, 1800, 1810, 1812, 1818, 1822, 1828, 1836, 1840, 1842, 1846, 1848, 1852, 1860, 1866, 1870, 1876, 1878, 1882, 1888, 1890]

private theorem leftChain : leftList.IsChain (· < ·) := by decide +kernel

private def leftSeats : Finset ℕ :=
  ⟨leftList, leftChain.pairwise.nodup⟩

set_option maxHeartbeats 30000000 in
-- Check the entire arithmetic remainder carrier, not only its card.
theorem left_carrier_checked : coarseTownPackingRemainder (primeScalesUpTo 10) 1031 = leftSeats := by
  change coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031 \ coarseTownDeletionVertices (primeScalesUpTo 10) 1031 = _
  rw [coarseTownDeletionVertices_eq_fibers]
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
  rw [town1031Seats_eq_production,oldPrimes1031_eq_production]
  decide +kernel

set_option maxHeartbeats 30000000 in
-- Actual supports are recomputed from divisibility over a kernel-certified carrier.
theorem left_represented_checked : (coarseTownRepresentedPrimes (primeScalesUpTo 10) 1031).card = 80 := by
  unfold coarseTownRepresentedPrimes representedDirections
  rw [left_carrier_checked]
  rw [show squareOffsetPrimeSupport 1031 = boundedSquareSupport 1031 from
    funext (squareOffsetPrimeSupport_eq_boundedSquareSupport 1031)]
  unfold boundedSquareSupport
  rw [oldPrimes1031_eq_production]
  decide +kernel

private def rightList : List ℕ := [6, 12, 16, 18, 22, 28, 30, 36, 40, 42, 46, 48, 58, 60, 70, 72, 78, 82, 96, 100, 102, 106, 118, 120, 126, 130, 132, 138, 142, 148, 162, 172, 180, 186, 190, 196, 198, 208, 216, 228, 232, 238, 240, 250, 252, 258, 268, 280, 282, 286, 312, 316, 328, 340, 342, 358, 366, 390, 408, 418, 436, 438, 448, 460, 462, 466, 468, 480, 492, 496, 502, 510, 516, 520, 522, 532, 540, 546, 550, 562, 568, 580, 586, 588, 592, 600, 606, 622, 630, 636, 642, 646, 648, 652, 658, 666, 676, 688, 700, 732, 736, 748, 756, 760, 762, 768, 778, 786, 796, 810, 820, 828, 840, 852, 862, 870, 876, 886, 888, 898, 910, 912, 930, 936, 942, 952, 958, 960, 966, 1000, 1002, 1006, 1008, 1012, 1026, 1038, 1056, 1068, 1092, 1098, 1108, 1110, 1126, 1138, 1150, 1156, 1170, 1192, 1198, 1216, 1218, 1230, 1236, 1240, 1282, 1288, 1296, 1302, 1308, 1320, 1350, 1356, 1360, 1372, 1378, 1380, 1398, 1416, 1422, 1446, 1450, 1462, 1470, 1488, 1506, 1510, 1512, 1516, 1540, 1546, 1558, 1560, 1572, 1588, 1626, 1632, 1638, 1668, 1692, 1702, 1708, 1710, 1720, 1728, 1738, 1758, 1770, 1776, 1782, 1786, 1792, 1810, 1822, 1836, 1840, 1842, 1852, 1866, 1876, 1878]

private theorem rightChain : rightList.IsChain (· < ·) := by decide +kernel

private def rightSeats : Finset ℕ :=
  ⟨rightList, rightChain.pairwise.nodup⟩

set_option maxHeartbeats 30000000 in
-- Check the entire arithmetic remainder carrier, not only its card.
theorem right_carrier_checked : coarseTownRightPackingRemainder (primeScalesUpTo 10) 1031 = rightSeats := by
  change coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031 \ coarseTownRightDeletionVertices (primeScalesUpTo 10) 1031 = _
  rw [coarseTownRightDeletionVertices_eq_fibers]
  unfold coarseTownRightDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
  rw [town1031Seats_eq_production,oldPrimes1031_eq_production]
  decide +kernel

set_option maxHeartbeats 30000000 in
-- Actual supports are recomputed from divisibility over a kernel-certified carrier.
theorem right_represented_checked : (coarseTownRightRepresentedPrimes (primeScalesUpTo 10) 1031).card = 75 := by
  unfold coarseTownRightRepresentedPrimes representedDirections
  rw [right_carrier_checked]
  rw [show squareOffsetPrimeSupport 1031 = boundedSquareSupport 1031 from
    funext (squareOffsetPrimeSupport_eq_boundedSquareSupport 1031)]
  unfold boundedSquareSupport
  rw [oldPrimes1031_eq_production]
  decide +kernel

theorem right_remainder_card_checked :
    (coarseTownRightPackingRemainder (primeScalesUpTo 10) 1031).card = 210 := by
  rw [right_carrier_checked]
  decide +kernel

theorem left_loss_decomposition_checked :
    coarseTownSupportLoss (primeScalesUpTo 10) 1031 = 56 ∧
      (coarseTownUnrepresentedActivePrimes (primeScalesUpTo 10) 1031).card = 48 ∧
      coarseTownRetainedSupportExcess (primeScalesUpTo 10) 1031 = 8 := by
  have hS := knownPrimeScales_primeScalesUpTo 10
  have hl := coarseTown_remainder_add_loss_eq_uncovered_add_active hS 1031
  have hd := coarseTown_loss_decomposition hS 1031
  have hp := coarseTown_active_card_partition hS 1031
  rw [remainder1031_card,uncovered1031_checked,active1031_checked] at hl
  rw [left_represented_checked,active1031_checked] at hp
  omega

theorem right_loss_decomposition_checked :
    coarseTownRightSupportLoss (primeScalesUpTo 10) 1031 = 62 ∧
      (coarseTownRightUnrepresentedActivePrimes (primeScalesUpTo 10) 1031).card = 53 ∧
      coarseTownRightRetainedSupportExcess (primeScalesUpTo 10) 1031 = 9 := by
  have hS := knownPrimeScales_primeScalesUpTo 10
  have hl := coarseTownRight_remainder_add_loss hS 1031
  have hd := coarseTownRight_loss_decomposition hS 1031
  have hp := coarseTownRight_active_card_partition hS 1031
  rw [right_remainder_card_checked,uncovered1031_checked,active1031_checked] at hl
  rw [right_represented_checked,active1031_checked] at hp
  omega

theorem better_orientation_checked :
    coarseTownBetterRemainder (primeScalesUpTo 10) 1031 =
      coarseTownPackingRemainder (primeScalesUpTo 10) 1031 := by
  unfold coarseTownBetterRemainder
  rw [remainder1031_card,right_remainder_card_checked]
  rfl

theorem better_cards_checked :
    (coarseTownBetterRemainder (primeScalesUpTo 10) 1031).card = 216 ∧
      coarseTownBetterLoss (primeScalesUpTo 10) 1031 = 56 := by
  rw [card_coarseTownBetterRemainder]
  unfold coarseTownBetterLoss
  rw [remainder1031_card,right_remainder_card_checked,
    left_loss_decomposition_checked.1,right_loss_decomposition_checked.1]
  decide +kernel

theorem exists_prime_squareCell_1031_of_better_selector : ∃ p, p.Prime ∧ SquareCell 1031 p := by
  apply exists_prime_squareCell_of_coarseTownBetter_deficit (knownPrimeScales_primeScalesUpTo 10) (by decide)
  rw [outside1031_card_checked,better_cards_checked.1]
  decide +kernel

end DkMathTest.LegendreRetained1031Calibration
