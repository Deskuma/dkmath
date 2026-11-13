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


example (n : ℕ) : outerApprox n =
    areaApprox n / (QuadrantUnitKernel.sequence (n+1)).core ^ 2 :=
  outerApprox_eq_areaApprox_div_core_sq n

example (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasurableSet (intrinsicOriginTriangle n j) := intrinsicOriginTriangle_measurable n j

example (n : ℕ)
    (harea : MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n)) :
    MeasureTheory.volume (intrinsicPolygonOuterRegion n) = ENNReal.ofReal (outerApprox n) :=
  intrinsicPolygonOuterRegion_volume_of_region n harea

example
    (harea : ∀ n, MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n))
    (hcover : ∀ n, Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion n) :
    MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) = intrinsicPi :=
  disk_measureReal_eq_intrinsicPi_of_polygon_sandwich harea hcover


example (n : ℕ) : (0 : EuclideanPlane) ∈ intrinsicPolygonRegion n :=
  intrinsicPolygonRegion_origin_mem n

example (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicOriginTriangle n j ⊆ intrinsicPolygonRegion n :=
  intrinsicOriginTriangle_subset_region_unconditional n j

example (n : ℕ) (j : Fin (dyadicSides n)) :
    ‖midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))‖ =
      (QuadrantUnitKernel.sequence (n + 1)).core := intrinsicPolygon_edge_midpoint_norm n j

example (n : ℕ) :
    Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion n ↔
      Metric.closedBall (0 : EuclideanPlane) (QuadrantUnitKernel.sequence (n + 1)).core ⊆
        intrinsicPolygonRegion n := closedBall_subset_outerRegion_iff_innerBall_subset n

example (n : ℕ) (j : Fin (dyadicSides n)) :
    originTriangleLinearMap n j '' standardTriangle = intrinsicOriginTriangle n j :=
  originTriangleLinearMap_image n j

example (n : ℕ) (j : Fin (dyadicSides n)) :
    (originTriangleMatrix n j).det = (QuadrantUnitKernel.sequence n).beam :=
  originTriangleMatrix_det n j


example (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((QuadrantUnitKernel.sequence n).beam) * MeasureTheory.volume standardTriangle :=
  intrinsicOriginTriangle_volume_eq_beam_mul_standard n j


example (n : ℕ) (j : Fin (dyadicSides n))
    (h : MeasureTheory.volume standardTriangle = ENNReal.ofReal (1 / 2)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((QuadrantUnitKernel.sequence n).beam / 2) :=
  intrinsicOriginTriangle_volume_of_standard n j h


example : MeasureTheory.volume standardTriangle = ENNReal.ofReal (1 / 2) :=
  standardTriangle_volume

example (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((QuadrantUnitKernel.sequence n).beam / 2) :=
  intrinsicOriginTriangle_volume n j

example (n : ℕ) :
    Metric.closedBall (0 : EuclideanPlane) (QuadrantUnitKernel.sequence (n + 1)).core ⊆
      intrinsicEdgeHalfSpaces n := intrinsicInnerBall_subset_edgeHalfSpaces n


example (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (intrinsicOriginTriangle n j)
      (intrinsicOriginTriangle n (intrinsicOppositeIndex n j)) :=
  intrinsicOriginTriangle_aedisjoint_opposite n j

example (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (intrinsicOriginTriangle n j)
      (intrinsicOriginTriangle n (regularVertexNext (dyadicSides_pos n) j)) :=
  intrinsicOriginTriangle_aedisjoint_next n j

example : MeasureTheory.volume (intrinsicOriginFan 0) = ENNReal.ofReal 2 :=
  intrinsicOriginFan_zero_volume

example (n : ℕ) : 0 < MeasureTheory.volume (intrinsicPolygonRegion n) :=
  intrinsicPolygonRegion_volume_pos n


example : intrinsicPolygonRegion 0 = intrinsicOriginFan 0 :=
  intrinsicPolygonRegion_zero_eq_originFan

example : MeasureTheory.volume (intrinsicPolygonRegion 0) = ENNReal.ofReal 2 :=
  intrinsicPolygonRegion_zero_volume

example : Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion 0 :=
  closedBall_subset_intrinsicPolygonOuterRegion_zero

example (n : ℕ) : orderOf (QuadrantUnitKernel.sequence n).kernel = 4 * 2 ^ n :=
  QuadrantUnitKernel.sequence_kernel_orderOf n

example (n : ℕ) : Function.Injective (QuadrantUnitKernel.directVertex n) :=
  QuadrantUnitKernel.directVertex_injective n

example (n : ℕ) (j : Fin (dyadicSides n)) :
    QuadrantUnitKernel.directVertex n j = regularVertex (dyadicSides n) j :=
  directVertex_eq_regularVertex n j

end DkMathTest.CosmicFormula.Rotation.CF2D
