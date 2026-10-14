/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonRepeatedBaseAggregate
import DkMathTest.NumberTheory.GnomonRepeatedCarryPhaseCalibration

#print "file: DkMathTest.NumberTheory.GnomonRepeatedBaseAggregateCalibration"

namespace DkMathTest.NumberTheory.GnomonRepeatedBaseAggregateCalibration
open DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- A composite integer base is deliberately admitted by the endpoint bound. -/
theorem composite_window69_checked :
    gnomonRepeatedSquareWindow 69 34 = {12} ∧ ¬ Nat.Prime 12 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem composite12_aggregate69 : 12 ∈ gnomonRepeatedAggregateBases 69 := by
  have hk : 34 ∈ Finset.Icc 2 (69 - 1) := by simp
  have hp : 12 ∈ gnomonRepeatedSquareWindow 69 34 := by
    rw [composite_window69_checked.1]
    exact Finset.mem_singleton_self _
  exact gnomonRepeatedSquareWindow_subset_aggregate (n := 69) (k := 34) hk hp

/-- The small region also drops activity, admitting the previously excluded base 5. -/
theorem small_inactive69_checked :
    5 ∈ gnomonRepeatedSmallBases 69 ∧ ¬ gnomonRepeatedBaseActive 69 5 := by
  simp only [gnomonRepeatedSmallBases, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

theorem composite12_positive_weight : 0 < gnomonRepeatedBaseWeight 69 12 := by
  have he : gnomonRepeatedBaseExponents 69 12 = {2, 3} := by decide +kernel
  unfold gnomonRepeatedBaseWeight
  rw [he]
  have hc : ({2, 3} : Finset ℕ).card = 2 := by decide +kernel
  rw [hc]
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

set_option maxRecDepth 4096 in
/-- Composite extra mass shows the aggregate is not merely the exact base reindexing. -/
theorem strict_aggregate_overcover69 :
    gnomonRepeatedPhaseBudget 69 < gnomonRepeatedAggregateBudget 69 := by
  have hnot : 12 ∉ gnomonRepeatedActiveBases 69 := by
    simp only [gnomonRepeatedActiveBases, Finset.mem_filter, Finset.mem_Icc]
    decide +kernel
  have h := gnomonRepeatedPhaseBudget_add_extra_le_aggregate (n := 69) (p := 12) (by norm_num : 3 ≤ 69)
    composite12_aggregate69 hnot
  have hp := composite12_positive_weight
  linarith

/-- Every required large anchor has its square-base route fixed by endpoint arithmetic. -/
theorem anchor_windows_checked :
    gnomonRepeatedSquareWindow 32 2 = {23} ∧
    gnomonRepeatedSquareWindow 69 5 = {31} ∧
    gnomonRepeatedSquareWindow 297 40 = {47} ∧
    gnomonRepeatedSquareWindow 1031 6 = {421} ∧
    gnomonRepeatedSquareWindow 2896 89 = {307} ∧
    gnomonRepeatedSquareWindow 5000 3 = {2887} := by
  decide +kernel

theorem base2_small2896_checked : 2 ∈ gnomonRepeatedSmallBases 2896 := by
  simp only [gnomonRepeatedSmallBases, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

theorem base2_ten_exponents2896 :
    gnomonRepeatedBaseExponents 2896 2 = Finset.Icc 13 22 ∧
    gnomonRepeatedBaseWeight 2896 2 = 10 * Real.log (2 : ℝ) := by
  have h := GnomonRepeatedCarryPhaseCalibration.base2_2896_checked
  constructor
  · change Finset.Icc (gnomonRepeatedFirstExponent 2896 2) (Nat.log 2 (2896 ^ 2)) = _
    rw [h.1, h.2.2]
  · unfold gnomonRepeatedBaseWeight gnomonRepeatedBaseExponents
    rw [h.1, h.2.2]
    norm_num

theorem fiber2896_retained :
    gnomonLargeCarryExponents 2896 2 8388608 = Finset.Icc 13 22 ∧
    (gnomonLargeCarryExponents 2896 2 8388608).card = 10 :=
  GnomonRepeatedCarryPhaseCalibration.fiber2896_retained

/-- The empty repeated-carry anchor is allowed a harmless small-base overestimate. -/
theorem trivial_anchor3_checked :
    gnomonRepeatedSquareWindow 3 2 = ∅ ∧ gnomonRepeatedSmallBases 3 = {2} := by
  decide +kernel

end DkMathTest.NumberTheory.GnomonRepeatedBaseAggregateCalibration
