/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity
import DkMathTest.NumberTheory.LegendreFullTownRegression
import DkMathTest.NumberTheory.LegendreDeletion1031Data

#print "file: DkMathTest.NumberTheory.LegendreDeletion1031Calibration"

namespace DkMathTest.LegendreDeletion1031Calibration

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMathTest.LegendreDeletion1031Data

set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Bounded arithmetic and prime-fiber maxima need a larger kernel reduction budget.
theorem deletion1031_card_checked :
    (coarseTownDeletionByFibers (primeScalesUpTo 10) 1031).card = 216 := by
  unfold coarseTownDeletionByFibers coarseTownDivisibilityFiber oldSupportSeatFiber
  rw [town1031Seats_eq_production, oldPrimes1031_eq_production]
  decide +kernel

theorem deletion1031_symbolic_card :
    (coarseTownDeletionVertices (primeScalesUpTo 10) 1031).card = 216 := by
  rw [coarseTownDeletionVertices_eq_fibers]
  exact deletion1031_card_checked

set_option maxHeartbeats 2000000 in
-- The complete bounded prime inventory is kernel-evaluated.
theorem oldPrimes1031_card_checked : (primeScalesUpTo 1031).card = 173 := by
  rw [oldPrimes1031_eq_production]
  exact oldPrimes1031_card

theorem remainder1031_card :
    (coarseTownPackingRemainder (primeScalesUpTo 10) 1031).card = 216 := by
  rw [card_coarseTownPackingRemainder,
    DkMathTest.LegendreFullTownRegression.large_anchor_grid.2.2, deletion1031_symbolic_card]

theorem exists_prime_squareCell_1031_of_coarseTownDeletion : ∃ p, p.Prime ∧ SquareCell 1031 p := by
  apply exists_prime_squareCell_of_coarseTown_deletion_deficit (primeScalesUpTo 10) (by decide)
  rw [oldPrimes1031_card_checked, deletion1031_symbolic_card,
    DkMathTest.LegendreFullTownRegression.large_anchor_grid.2.2]
  decide +kernel

end DkMathTest.LegendreDeletion1031Calibration
