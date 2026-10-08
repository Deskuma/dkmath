/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonPooledThresholdAudit
import DkMathTest.NumberTheory.GnomonCentralCarryCompensationCalibration

#print "file: DkMathTest.NumberTheory.GnomonPooledThresholdCalibration"

namespace DkMathTest.NumberTheory.GnomonPooledThresholdCalibration
open DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- The canonical threshold rule handles the cross-base example at 4. -/
theorem pooling4_checked : gnomonThresholdPooledCompensation 4 := by
  unfold gnomonThresholdPooledCompensation
  decide +kernel

theorem central4_checked : gnomonPascalSmallCarryMass 4 ≤ Real.log (Nat.choose 8 4 : ℝ) :=
  gnomonSmallCarry_le_central_of_thresholdPooling (by norm_num) pooling4_checked

theorem pointwise4_retained : gnomonLowDivisorCarryBit 4 3 = 1 ∧
    ¬ 3 ≤ 4 % 3 + 4 % 3 ∧ (Nat.choose 8 4).factorization 3 = 0 :=
  GnomonCentralCarryCompensationCalibration.pointwise4_retained

theorem products4_retained :
    (∏ d ∈ gnomonSmallOnlyCarryEvents 4, d.minFac) = 3 ∧
    (∏ d ∈ gnomonCentralOnlyCarryEvents 4, d.minFac) = 70 ∧
    3 ≤ 70 ∧ ¬ 3 ∣ 70 :=
  GnomonCentralCarryCompensationCalibration.products4_checked

/-- A lower pool pays the high-pool deficit; neither side is collapsed into one block. -/
theorem pools27_checked :
    gnomonResidualThresholdProduct (gnomonSmallOnlyCarryEvents 27) 8 = 4807 ∧
    gnomonResidualThresholdProduct (gnomonCentralOnlyCarryEvents 27) 8 = 2491 ∧
    (∏ d ∈ (gnomonSmallOnlyCarryEvents 27).filter (fun d => d.minFac < 8), d.minFac) = 5 ∧
    (∏ d ∈ (gnomonCentralOnlyCarryEvents 27).filter (fun d => d.minFac < 8), d.minFac) = 392 := by
  decide +kernel

theorem total27_still_holds :
    (∏ d ∈ gnomonSmallOnlyCarryEvents 27, d.minFac) ≤
      ∏ d ∈ gnomonCentralOnlyCarryEvents 27, d.minFac := by
  have h := GnomonCentralCarryCompensationCalibration.products27_checked
  rw [h.1, h.2]
  norm_num

theorem no_dominating_injection27_retained : ¬ ∃ f : ℕ → ℕ,
    Set.InjOn f (↑(gnomonSmallOnlyCarryEvents 27)) ∧
    (∀ d ∈ gnomonSmallOnlyCarryEvents 27,
      f d ∈ gnomonCentralOnlyCarryEvents 27 ∧ d.minFac ≤ (f d).minFac) :=
  GnomonCentralCarryCompensationCalibration.no_dominating_injection27

/-- All anchors have an exact high/low split; no capacity sign is assumed. -/
theorem anchor_pool_split {n : ℕ}
    (_hn : n ∈ ({4, 27, 32, 69, 210, 297, 1031, 5000} : Finset ℕ)) (t : ℕ) :
    (∏ d ∈ gnomonSmallOnlyCarryEvents n, d.minFac) =
      gnomonResidualThresholdProduct (gnomonSmallOnlyCarryEvents n) t *
        ∏ d ∈ (gnomonSmallOnlyCarryEvents n).filter (fun d => d.minFac < t), d.minFac :=
  gnomonResidualThresholdProduct_split _ t

end DkMathTest.NumberTheory.GnomonPooledThresholdCalibration
