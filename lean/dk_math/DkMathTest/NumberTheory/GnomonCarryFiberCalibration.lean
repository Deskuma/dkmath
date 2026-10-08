/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCarryFiber
import DkMathTest.NumberTheory.GnomonDivisorCarryCalibration

#print "file: DkMathTest.NumberTheory.GnomonCarryFiberCalibration"

namespace DkMathTest.NumberTheory.GnomonCarryFiberCalibration

open DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- The first large-label collision consists of two consecutive exponents. -/
theorem fiber11_two_checked : gnomonLargeCarryExponents 11 2 128 = {5, 6} := by
  decide +kernel

/-- The target valuation removes a possible old exponent at the first slack anchor. -/
theorem fiber6_slack_checked : gnomonLargeCarryExponents 6 2 48 = {4} ∧
    Nat.log 2 (6 ^ 2) - Nat.log 2 (2 * 6) = 2 ∧ (48 : ℕ).factorization 2 = 4 := by
  decide +kernel

/-- The same-base weight is exactly one log per exponent, including collisions. -/
theorem fiber11_weight_checked :
    (∑ a ∈ gnomonLargeCarryExponents 11 2 128, ArithmeticFunction.vonMangoldt (2 ^ a)) =
      2 * Real.log 2 := by
  rw [gnomonLargeCarryExponents_weight (by omega) (by norm_num) (by norm_num [SquareCell])]
  have hv : (128 : ℕ).factorization 2 = 7 := by decide +kernel
  rw [hv]
  norm_num

/-- The cutoff cap is strictly larger than the actual first slack fiber. -/
theorem fiber6_weight_strict_cap_checked :
    (∑ a ∈ gnomonLargeCarryExponents 6 2 48, ArithmeticFunction.vonMangoldt (2 ^ a)) =
      Real.log 2 ∧
    Real.log (2 : ℝ) <
      ((Nat.log 2 (6 ^ 2) - Nat.log 2 (2 * 6) : ℕ) : ℝ) * Real.log 2 := by
  constructor
  · rw [gnomonLargeCarryExponents_weight (by omega) (by norm_num) (by norm_num [SquareCell])]
    rw [fiber6_slack_checked.2.2]
    norm_num
  · have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    norm_num
    linarith

/-- An old cutoff excludes the target's own higher power. -/
theorem fiber5_checked : gnomonLargeCarryExponents 5 2 32 = {4} := by
  decide +kernel

/-- A valuation cutoff can precede the old-label cutoff. -/
theorem fiber11_three_checked : gnomonLargeCarryExponents 11 3 135 = {3} := by
  decide +kernel

/-- The preserved 297 label belongs to a singleton exponent fiber. -/
theorem fiber297_checked : gnomonLargeCarryExponents 297 5 88750 = {4} := by
  decide +kernel

/-- Three old same-base labels share one target at anchor 1031. -/
theorem fiber1031_checked : gnomonLargeCarryExponents 1031 2 1064960 = {12, 13, 14} := by
  decide +kernel

/-- The largest collision in the inherited range is a ten-exponent chain. -/
theorem fiber2896_checked :
    gnomonLargeCarryExponents 2896 2 8388608 = Finset.Icc 13 22 := by
  decide +kernel

theorem fiber2896_card_checked : (gnomonLargeCarryExponents 2896 2 8388608).card = 10 := by
  rw [fiber2896_checked]
  decide +kernel

/-- No event remains when target valuation lies below the large threshold. -/
theorem empty_fiber_checked : gnomonLargeCarryExponents 3 2 12 = ∅ := by
  decide +kernel

/-- Dropping the large-band condition permits mixed prime bases at a shared image. -/
theorem mixed_base7_checked :
    3 ∈ gnomonPascalLowCarryEvents 7 ∧ 17 ∈ gnomonPascalLowCarryEvents 7 ∧
    (3 : ℕ).minFac ≠ (17 : ℕ).minFac ∧
    gnomonNextShellMultiple 7 3 = 51 ∧ gnomonNextShellMultiple 7 17 = 51 ∧
    SquareCell 7 51 := by
  unfold SquareCell
  decide +kernel

/-- This is the first positive anchor with mixed bases for the next-multiple map. -/
theorem earlier_no_mixed_bases_checked :
    ∀ n ∈ Finset.Icc 1 6, ∀ d ∈ gnomonPascalLowCarryEvents n,
      ∀ e ∈ gnomonPascalLowCarryEvents n,
        gnomonNextShellMultiple n d = gnomonNextShellMultiple n e → d.minFac = e.minFac := by
  decide +kernel

/-- One base log per target undercounts the first large collision fiber. -/
theorem one_weight_per_target_fails_checked :
    ¬ ((gnomonLargeCarryExponents 11 2 128).card : ℝ) * Real.log 2 ≤ Real.log 2 := by
  have hc : (gnomonLargeCarryExponents 11 2 128).card = 2 := by
    rw [fiber11_two_checked]; decide +kernel
  rw [hc]
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  norm_num
  linarith

end DkMathTest.NumberTheory.GnomonCarryFiberCalibration
