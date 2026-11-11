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

example : Tendsto (fun n => outerApprox n - areaApprox n) atTop (𝓝 0) :=
  tendsto_outer_sub_area_zero

example (n : ℕ) : intrinsicPolygonPerimeter n / 2 = areaApprox (n+1) := by
  rw [intrinsicPolygonPerimeter_div_two, halfPerimeterApprox_eq_areaApprox_succ]

end DkMathTest.CosmicFormula.Rotation.CF2D
