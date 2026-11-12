/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D

#print "file: DkMathTest.CosmicFormula.Rotation.CF2D.IntrinsicPiReview"

/-! 二分核の内外評価と正方形・八角形の幾何的な回帰例。 -/
namespace DkMathTest.CosmicFormula.Rotation.CF2D
open DkMath.CosmicFormula.Rotation.CF2D
open Filter
open scoped Topology

example : dyadicSides 0 = 4 := by norm_num [dyadicSides]
example : dyadicSides 1 = 8 := by norm_num [dyadicSides]

example : intrinsicPolygonSignedArea 0 = 2 := by
  rw [intrinsicPolygonSignedArea_eq_areaApprox, areaApprox_zero]

example : intrinsicPolygonSignedArea 1 = 2 * Real.sqrt 2 := by
  rw [intrinsicPolygonSignedArea_eq_areaApprox, areaApprox_one]

example : intrinsicPolygonPerimeter 0 / 2 = 2 * Real.sqrt 2 := by
  rw [intrinsicPolygonPerimeter_div_two, halfPerimeterApprox_zero]

example (n : ℕ) : areaApprox n ≤ intrinsicPi ∧ intrinsicPi ≤ outerApprox n :=
  intrinsicPi_bounds n

example (n : ℕ) : intrinsicPi - areaApprox n ≤ 8 * (1 / 2 : ℝ) ^ n :=
  intrinsicPi_sub_areaApprox_le n

example (n : ℕ) : 0 ≤ intrinsicPi - areaApprox n ∧
    intrinsicPi - areaApprox n ≤ 8 * (1 / 4 : ℝ) ^ n :=
  intrinsicPi_sub_areaApprox_le_quarter_pow n

example (n : ℕ) : 0 ≤ outerApprox n - intrinsicPi ∧
    outerApprox n - intrinsicPi ≤ 8 * (1 / 4 : ℝ) ^ n :=
  outerApprox_sub_intrinsicPi_le_quarter_pow n

example : outerApprox 2 - areaApprox 2 ≤ (1 / 2 : ℝ) := by
  have h := outerApprox_sub_areaApprox_le_quarter_pow 2
  norm_num at h
  linarith

example (n : ℕ) : MeasurableSet (intrinsicPolygonRegion n) :=
  intrinsicPolygonRegion_measurable n

example (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicPolygonFanTriangle n j ⊆ intrinsicPolygonRegion n :=
  intrinsicPolygonFanTriangle_subset_region n j

example (n : ℕ) : intrinsicPolygonRegion n ⊆ Metric.closedBall (0 : EuclideanPlane) 1 :=
  intrinsicPolygonRegion_subset_closedBall n

example (n : ℕ) : MeasureTheory.volume (intrinsicPolygonRegion n) ≤ ENNReal.ofReal intrinsicPi :=
  intrinsicPolygonRegion_volume_le_intrinsicPi n

example : Tendsto (fun n => outerApprox n - areaApprox n) atTop (𝓝 0) :=
  tendsto_outer_sub_area_zero

example (n : ℕ) : intrinsicPolygonPerimeter n / 2 = areaApprox (n+1) := by
  rw [intrinsicPolygonPerimeter_div_two, halfPerimeterApprox_eq_areaApprox_succ]

end DkMathTest.CosmicFormula.Rotation.CF2D
