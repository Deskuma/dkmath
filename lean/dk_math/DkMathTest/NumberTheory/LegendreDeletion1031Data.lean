/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

#print "file: DkMathTest.NumberTheory.LegendreDeletion1031Data"

namespace DkMathTest.LegendreDeletion1031Data

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive

set_option maxRecDepth 100000

/-- Sorted arithmetic carrier; adjacent comparisons certify distinctness. -/
def town1031SeatsList : List ℕ :=
  [
    6, 12, 16, 18, 22, 28, 30, 36, 40, 42, 46, 48, 58, 60,
    70, 72, 76, 78, 82, 88, 90, 96, 100, 102, 106, 112, 118, 120,
    126, 130, 132, 138, 142, 148, 156, 160, 162, 166, 168, 172, 180, 186,
    190, 196, 198, 202, 208, 210, 216, 222, 226, 228, 232, 238, 240, 246,
    250, 252, 256, 258, 268, 270, 280, 282, 286, 288, 292, 298, 300, 306,
    310, 312, 316, 322, 328, 330, 336, 340, 342, 348, 352, 358, 366, 370,
    372, 376, 378, 382, 390, 396, 400, 406, 408, 412, 418, 420, 426, 432,
    436, 438, 442, 448, 450, 456, 460, 462, 466, 468, 478, 480, 490, 492,
    496, 498, 502, 508, 510, 516, 520, 522, 526, 532, 538, 540, 546, 550,
    552, 558, 562, 568, 576, 580, 582, 586, 588, 592, 600, 606, 610, 616,
    618, 622, 628, 630, 636, 642, 646, 648, 652, 658, 660, 666, 670, 672,
    676, 678, 688, 690, 700, 702, 706, 708, 712, 718, 720, 726, 730, 732,
    736, 742, 748, 750, 756, 760, 762, 768, 772, 778, 786, 790, 792, 796,
    798, 802, 810, 816, 820, 826, 828, 832, 838, 840, 846, 852, 856, 858,
    862, 868, 870, 876, 880, 882, 886, 888, 898, 900, 910, 912, 916, 918,
    922, 928, 930, 936, 940, 942, 946, 952, 958, 960, 966, 970, 972, 978,
    982, 988, 996, 1000, 1002, 1006, 1008, 1012, 1020, 1026, 1030, 1036, 1038, 1042,
    1048, 1050, 1056, 1062, 1066, 1068, 1072, 1078, 1080, 1086, 1090, 1092, 1096, 1098,
    1108, 1110, 1120, 1122, 1126, 1128, 1132, 1138, 1140, 1146, 1150, 1152, 1156, 1162,
    1168, 1170, 1176, 1180, 1182, 1188, 1192, 1198, 1206, 1210, 1212, 1216, 1218, 1222,
    1230, 1236, 1240, 1246, 1248, 1252, 1258, 1260, 1266, 1272, 1276, 1278, 1282, 1288,
    1290, 1296, 1300, 1302, 1306, 1308, 1318, 1320, 1330, 1332, 1336, 1338, 1342, 1348,
    1350, 1356, 1360, 1362, 1366, 1372, 1378, 1380, 1386, 1390, 1392, 1398, 1402, 1408,
    1416, 1420, 1422, 1426, 1428, 1432, 1440, 1446, 1450, 1456, 1458, 1462, 1468, 1470,
    1476, 1482, 1486, 1488, 1492, 1498, 1500, 1506, 1510, 1512, 1516, 1518, 1528, 1530,
    1540, 1542, 1546, 1548, 1552, 1558, 1560, 1566, 1570, 1572, 1576, 1582, 1588, 1590,
    1596, 1600, 1602, 1608, 1612, 1618, 1626, 1630, 1632, 1636, 1638, 1642, 1650, 1656,
    1660, 1666, 1668, 1672, 1678, 1680, 1686, 1692, 1696, 1698, 1702, 1708, 1710, 1716,
    1720, 1722, 1726, 1728, 1738, 1740, 1750, 1752, 1756, 1758, 1762, 1768, 1770, 1776,
    1780, 1782, 1786, 1792, 1798, 1800, 1806, 1810, 1812, 1818, 1822, 1828, 1836, 1840,
    1842, 1846, 1848, 1852, 1860, 1866, 1870, 1876, 1878, 1882, 1888, 1890]

def town1031Seats : Finset ℕ :=
  ⟨town1031SeatsList, by
    apply List.Pairwise.nodup (r := fun a b : ℕ => a < b)
    apply List.IsChain.pairwise
    decide +kernel⟩

@[simp] theorem mem_town1031Seats {a : ℕ} : a ∈ town1031Seats ↔ a ∈ town1031SeatsList := Iff.rfl

/-- Sorted arithmetic carrier; adjacent comparisons certify distinctness. -/
def oldPrimes1031List : List ℕ :=
  [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
    47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
    109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
    269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
    353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
    439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521,
    523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
    617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
    709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
    811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887,
    907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
    1009, 1013, 1019, 1021, 1031]

def oldPrimes1031 : Finset ℕ :=
  ⟨oldPrimes1031List, by
    apply List.Pairwise.nodup (r := fun a b : ℕ => a < b)
    apply List.IsChain.pairwise
    decide +kernel⟩

@[simp] theorem mem_oldPrimes1031 {a : ℕ} : a ∈ oldPrimes1031 ↔ a ∈ oldPrimes1031List := Iff.rfl

/-- Sorted arithmetic carrier; adjacent comparisons certify distinctness. -/
def base1031SeatsList : List ℕ :=
  [
    6, 12, 16, 18, 22, 28, 30, 36, 40, 42, 46, 48, 58, 60,
    70, 72, 76, 78, 82, 88, 90, 96, 100, 102, 106, 112, 118, 120,
    126, 130, 132, 138, 142, 148, 156, 160, 162, 166, 168, 172, 180, 186,
    190, 196, 198, 202, 208, 210]

def base1031Seats : Finset ℕ :=
  ⟨base1031SeatsList, by
    apply List.Pairwise.nodup (r := fun a b : ℕ => a < b)
    apply List.IsChain.pairwise
    decide +kernel⟩

@[simp] theorem mem_base1031Seats {a : ℕ} : a ∈ base1031Seats ↔ a ∈ base1031SeatsList := Iff.rfl

theorem base1031_geometry_checked :
    primeWorldModulus (primeScalesUpTo 10) = 210 ∧
      coarsePrimeWorldPeriodCount (primeScalesUpTo 10) 1031 = 9 ∧
      coarsePrimeWorldBase (primeScalesUpTo 10) 1031 = base1031Seats := by
  decide +kernel

/-- Linear list equality checks the expansion, without all-pairs membership enumeration. -/
theorem town1031_list_expansion : town1031SeatsList =
    (List.range 9).flatMap (fun j => base1031SeatsList.map (fun r => r + j * 210)) := by
  decide +kernel

/-- The exact symbolic carrier follows from phased coordinates and the checked list expansion. -/
theorem town1031Seats_eq_production :
    coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031 = town1031Seats := by
  ext a
  rw [mem_coarsePrimeWorldFullTown, mem_town1031Seats, town1031_list_expansion]
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨r, hr, j, hj, he⟩
    rw [base1031_geometry_checked.2.2] at hr
    rw [base1031_geometry_checked.2.1] at hj
    rw [base1031_geometry_checked.1] at he
    exact ⟨j, hj, r, mem_base1031Seats.mp hr, he⟩
  · rintro ⟨j, hj, r, hr, he⟩
    refine ⟨r, ?_, j, ?_, ?_⟩
    · rw [base1031_geometry_checked.2.2]
      exact mem_base1031Seats.mpr hr
    · simpa only [base1031_geometry_checked.2.1] using hj
    · simpa only [base1031_geometry_checked.1] using he

set_option maxHeartbeats 2000000 in
-- This checks the entire bounded prime inventory, not externally supplied primality labels.
theorem oldPrimes1031_eq_production : primeScalesUpTo 1031 = oldPrimes1031 := by
  decide +kernel

theorem oldPrimes1031_card : oldPrimes1031.card = 173 := by
  decide +kernel

end DkMathTest.LegendreDeletion1031Data
