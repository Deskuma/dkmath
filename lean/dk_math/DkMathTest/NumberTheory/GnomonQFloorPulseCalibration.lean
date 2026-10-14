/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonQFloorPulse
import DkMathTest.NumberTheory.GnomonRepeatedCarryPhaseCalibration

#print "file: DkMathTest.NumberTheory.GnomonQFloorPulseCalibration"

namespace DkMathTest.NumberTheory.GnomonQFloorPulseCalibration
open DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Fixed pointwise pulse tests avoid enumerating quadratic prime bands. -/
theorem anchor_pulses_checked :
    gnomonShellMultipleCount 32 67 = 1 ∧
    gnomonShellMultipleCount 69 139 = 1 ∧
    gnomonShellMultipleCount 210 421 = 1 ∧
    gnomonShellMultipleCount 297 599 = 1 ∧
    gnomonShellMultipleCount 1031 2063 = 1 ∧
    gnomonShellMultipleCount 2896 5801 = 1 ∧
    gnomonShellMultipleCount 5000 10007 = 1 := by
  decide +kernel

theorem anchor_targets_checked :
    gnomonNextShellMultiple 32 67 = 1072 ∧
    gnomonNextShellMultiple 69 139 = 4865 ∧
    gnomonNextShellMultiple 210 421 = 44205 ∧
    gnomonNextShellMultiple 297 599 = 88652 ∧
    gnomonNextShellMultiple 1031 2063 = 1064508 ∧
    gnomonNextShellMultiple 2896 5801 = 8388246 ∧
    gnomonNextShellMultiple 5000 10007 = 25007493 := by
  decide +kernel

theorem qlabel69_checked : 139 ∈ gnomonQPrimeLabels 69 := by
  rw [mem_gnomonQPrimeLabels]
  simp only [gnomonQPrimeBand, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

/-- A carrying repeated power is expressly excluded from the prime-only currency. -/
theorem repeated_label_excluded69 :
    gnomonLowDivisorCarryBit 69 256 = 1 ∧ 256 ∉ gnomonQPrimeLabels 69 := by
  simp only [mem_gnomonQPrimeLabels, gnomonQPrimeBand, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

/-- New shell-prime birth is above the old cutoff and does not belong to Q. -/
theorem shell_birth_excluded32 :
    Nat.Prime 1031 ∧ SquareCell 32 1031 ∧
      gnomonLowDivisorCarryBit 32 1031 = 1 ∧ 1031 ∉ gnomonQPrimeLabels 32 := by
  simp only [mem_gnomonQPrimeLabels, gnomonQPrimeBand, Finset.mem_filter, Finset.mem_Icc,
    SquareCell]
  decide +kernel

theorem zero_pulse32_checked : gnomonShellMultipleCount 32 1019 = 0 := by
  decide +kernel

/-- A tiny exact target/cofactor product calibrates the natural-number currency. -/
theorem product3_checked :
    (∏ p ∈ gnomonQPrimeLabels 3, p) = 7 ∧
    (∏ p ∈ gnomonQPrimeLabels 3, (3 ^ 2 / p + 1)) = 2 ∧
    (∏ p ∈ gnomonQPrimeLabels 3, gnomonNextShellMultiple 3 p) = 14 := by
  decide +kernel

theorem capacity_failure_at_anchors {n : ℕ}
    (hn : n ∈ ({32, 69, 210, 297, 1031, 2896, 5000} : Finset ℕ)) :
    ¬ gnomonQTargetCapacityBudget n + gnomonRepeatPhaseCorrectionBudget n <
      Real.log (GnomonPascalCell n : ℝ) := by
  have hsmall : ∀ m ∈ ({32, 69, 210, 297, 1031, 2896, 5000} : Finset ℕ), 3 ≤ m := by
    decide +kernel
  exact gnomonQTargetCapacity_never_closes040 (hsmall n hn)

/-- Prime-only injection does not erase the old ten-power collision regression. -/
theorem repeated_fiber2896_retained :
    gnomonLargeCarryExponents 2896 2 8388608 = Finset.Icc 13 22 ∧
    (gnomonLargeCarryExponents 2896 2 8388608).card = 10 :=
  GnomonRepeatedCarryPhaseCalibration.fiber2896_retained

end DkMathTest.NumberTheory.GnomonQFloorPulseCalibration
