/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.OldSupportCapacityCertificate

#print "file: DkMathTest.NumberTheory.LegendreCapacity297Calibration"

namespace DkMathTest.LegendreCapacity297Calibration

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- Sorted discovered seats; the subsequent checker recomputes all actual prime waves. -/
def seats297 : Finset ℕ :=
  ([
    2, 4, 8, 10, 14, 20, 28, 32, 34, 50, 52, 58,
    62, 64, 70, 74, 80, 92, 94, 98, 112, 118, 128, 130,
    142, 148, 158, 164, 170, 172, 182, 184, 188, 190, 200, 202,
    212, 214, 218, 220, 224, 232, 238, 244, 254, 260, 262, 272,
    280, 284, 290, 304, 314, 322, 338, 340, 368, 370, 380, 382,
    394, 398, 400] : List ℕ).toFinset

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- The checker recomputes each bounded prime fiber of the supplied 63-seat family.
theorem certificate297_checked : checkOldSupportCapacityCertificate 297 seats297 = true := by
  decide +kernel

theorem certificate297_semantic : OldSupportCapacityCertificate 297 seats297 :=
  (checkOldSupportCapacityCertificate_eq_true_iff 297 seats297).mp certificate297_checked

theorem certificate297_cards : seats297.card = 63 ∧ (primeScalesUpTo 297).card = 62 := by
  decide +kernel

theorem exists_prime_squareCell_297_of_explicitCapacityCertificate :
    ∃ p, p.Prime ∧ SquareCell 297 p :=
  exists_prime_squareCell_of_oldSupportCapacityCertificate (by decide) certificate297_semantic

end DkMathTest.LegendreCapacity297Calibration
