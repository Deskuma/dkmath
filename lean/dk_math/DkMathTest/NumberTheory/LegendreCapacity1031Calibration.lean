/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreDeletion1031Data

#print "file: DkMathTest.NumberTheory.LegendreCapacity1031Calibration"

namespace DkMathTest.LegendreCapacity1031Calibration

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMathTest.LegendreDeletion1031Data

/-- Sorted discovery input; every support wave is subsequently recomputed. -/
def seats1031List : List ℕ :=
  [
    6, 12, 16, 18, 22, 28, 36, 40, 48, 58, 70, 72, 76, 78,
    82, 96, 100, 102, 106, 112, 118, 120, 126, 130, 132, 138, 142, 148,
    162, 172, 180, 186, 190, 196, 198, 210, 216, 228, 232, 238, 240, 246,
    250, 252, 258, 268, 280, 282, 286, 312, 316, 328, 330, 340, 342, 358,
    366, 378, 390, 408, 418, 436, 438, 448, 460, 462, 466, 468, 480, 492,
    496, 498, 502, 510, 516, 520, 522, 532, 540, 546, 550, 558, 562, 568,
    580, 586, 588, 592, 600, 606, 622, 630, 636, 642, 646, 648, 652, 658,
    666, 676, 688, 700, 708, 718, 726, 732, 736, 748, 756, 760, 762, 768,
    778, 786, 796, 798, 810, 820, 828, 832, 840, 852, 856, 862, 870, 876,
    880, 886, 888, 898, 910, 912, 918, 922, 930, 936, 942, 952, 958, 960,
    966, 1000, 1002, 1006, 1008, 1012, 1026, 1038, 1056, 1068, 1092, 1098, 1108, 1110,
    1126, 1138, 1140, 1150, 1156, 1162, 1170, 1192, 1198, 1216, 1218, 1230, 1236, 1240,
    1266, 1282, 1288, 1296, 1302, 1308, 1320, 1342, 1350, 1356, 1360, 1372, 1378, 1380,
    1398, 1402, 1416, 1420, 1422, 1446, 1450, 1458, 1462, 1470, 1488, 1506, 1510, 1512,
    1516, 1530, 1540, 1546, 1558, 1560, 1572, 1588, 1618, 1626, 1632, 1638, 1642, 1668,
    1678, 1692, 1702, 1708, 1710, 1720, 1728, 1738, 1758, 1770, 1776, 1782, 1786, 1792,
    1810, 1822, 1836, 1840, 1842, 1852, 1866, 1876, 1878]

def seats1031 : Finset ℕ :=
  ⟨seats1031List, by
    apply List.Pairwise.nodup (r := fun a b : ℕ => a < b)
    apply List.IsChain.pairwise
    decide +kernel⟩

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- The checked inventory avoids repeatedly reducing primality while arithmetic fibers are checked.
theorem certificate1031_checked : checkOldSupportCapacityCertificate 1031 seats1031 = true := by
  unfold checkOldSupportCapacityCertificate oldSupportSeatFiber
  rw [oldPrimes1031_eq_production]
  decide +kernel

theorem certificate1031_semantic : OldSupportCapacityCertificate 1031 seats1031 :=
  (checkOldSupportCapacityCertificate_eq_true_iff 1031 seats1031).mp certificate1031_checked

theorem certificate1031_cards : seats1031.card = 233 ∧ (primeScalesUpTo 1031).card = 173 := by
  constructor
  · decide +kernel
  · rw [oldPrimes1031_eq_production]
    exact oldPrimes1031_card

theorem exists_prime_squareCell_1031_of_explicitCapacityCertificate :
    ∃ p, p.Prime ∧ SquareCell 1031 p :=
  exists_prime_squareCell_of_oldSupportCapacityCertificate (by decide) certificate1031_semantic

end DkMathTest.LegendreCapacity1031Calibration
