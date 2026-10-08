/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation
import DkMathTest.NumberTheory.LegendreDeletion1031Calibration

#print "file: DkMathTest.NumberTheory.LegendreSurvivor1031Calibration"

namespace DkMathTest.LegendreSurvivor1031Calibration

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMathTest.LegendreDeletion1031Data DkMathTest.LegendreDeletion1031Calibration

set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem outside1031_card_checked : (coarseOutsidePrimes (primeScalesUpTo 10) 1031).card = 169 := by
  unfold coarseOutsidePrimes
  rw [oldPrimes1031_eq_production]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
/-- Sharper capacity consumer, retaining the original 021 endpoint unchanged. -/
theorem exists_prime_squareCell_1031_of_survivor_deletion : ∃ p, p.Prime ∧ SquareCell 1031 p := by
  apply exists_prime_squareCell_of_coarseTown_outside_deletion_deficit
    (knownPrimeScales_primeScalesUpTo 10) (by decide)
  rw [outside1031_card_checked, deletion1031_symbolic_card,
    DkMathTest.LegendreFullTownRegression.large_anchor_grid.2.2]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem incidence1031_checked : coarseFullTownIncidence (primeScalesUpTo 10) 1031 = 439 := by
  rw [coarseFullTownIncidence_eq_divisibility_sum]
  unfold coarseTownDivisibilityFiber oldSupportSeatFiber coarseOutsidePrimes
  rw [town1031Seats_eq_production, oldPrimes1031_eq_production]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem active1031_checked : (coarseFullTownActivePrimes (primeScalesUpTo 10) 1031).card = 128 := by
  rw [coarseFullTownActivePrimes_eq_divisibility_filter]
  unfold coarseTownDivisibilityFiber oldSupportSeatFiber coarseOutsidePrimes
  rw [town1031Seats_eq_production, oldPrimes1031_eq_production]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Bounded actual divisibility and carrier equality require additional kernel reductions.
theorem uncovered1031_checked : (coarseFullTownUncoveredSeats (primeScalesUpTo 10) 1031).card = 144 := by
  unfold coarseFullTownUncoveredSeats
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  unfold boundedSquareSupport
  rw [town1031Seats_eq_production, oldPrimes1031_eq_production]
  decide +kernel

theorem conservation1031_coordinates :
    coarseFullTownSupportExcess (primeScalesUpTo 10) 1031 = 151 ∧
      coarseTownDeletionMass (primeScalesUpTo 10) 1031 = 311 ∧
      coarseTownDeletionOverlap (primeScalesUpTo 10) 1031 = 95 := by
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess
    (knownPrimeScales_primeScalesUpTo 10) 1031
  have hm := coarseTownDeletionMass_add_active_eq_incidence (primeScalesUpTo 10) 1031
  have ho := card_deletion_add_overlap_eq_mass (knownPrimeScales_primeScalesUpTo 10) 1031
  rw [incidence1031_checked, uncovered1031_checked,
    DkMathTest.LegendreFullTownRegression.large_anchor_grid.2.2] at hs
  rw [active1031_checked, incidence1031_checked] at hm
  rw [deletion1031_symbolic_card] at ho
  omega

set_option linter.unnecessarySimpa false in
/-- Numeric normalization of the production identity: 216+151=144+128+95. -/
theorem master1031_checked : (216 : ℕ) + 151 = 144 + 128 + 95 := by
  simpa only [remainder1031_card, conservation1031_coordinates.1, uncovered1031_checked,
    active1031_checked, conservation1031_coordinates.2.2] using
    (coarseTown_remainder_conservation (knownPrimeScales_primeScalesUpTo 10) 1031)

end DkMathTest.LegendreSurvivor1031Calibration
