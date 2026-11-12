/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicRegularPolygon
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonMeasure"

/-!
# 正多角形の凸包と測度

有限軌道の頂点の凸包を、ユークリッド平面の実際の領域として定義する。
この領域はコンパクトかつ可測で、単位閉円盤に含まれる。したがってその測度は
単位円盤の測度以下である。

第１頂点を共有する三角形を定義し、各三角形が凸包に含まれることも示す。
靴紐和との等式はここでは主張しない。その証明には三角形の和が凸包に等しいこと、各三角形の
測度、および境界での重なりの扱いが別途必要である。また円盤の測度の表示には
既存の円周率との bridge を使うため、これは独立な円積率の証明ではない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D

/-- 正多角形の頂点の凸包を、測度を持つユークリッド平面の部分集合として定める。 -/
noncomputable def intrinsicPolygonRegion (n : ℕ) : Set EuclideanPlane :=
  convexHull ℝ (Set.range (intrinsicRegularPolygon n).vertices)

/-- 有限個の頂点の凸包なので、多角形領域はコンパクトである。 -/
theorem intrinsicPolygonRegion_compact (n : ℕ) : IsCompact (intrinsicPolygonRegion n) := by
  exact (Set.finite_range _).isCompact_convexHull ℝ

/-- 多角形領域はルベーグ可測である。 -/
theorem intrinsicPolygonRegion_measurable (n : ℕ) : MeasurableSet (intrinsicPolygonRegion n) :=
  (intrinsicPolygonRegion_compact n).isClosed.measurableSet

/-- 単位円上の頂点の凸包は、凸な単位閉円盤に含まれる。 -/
theorem intrinsicPolygonRegion_subset_closedBall (n : ℕ) :
    intrinsicPolygonRegion n ⊆ Metric.closedBall (0 : EuclideanPlane) 1 := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨j, rfl⟩
  exact Metric.sphere_subset_closedBall (intrinsicRegularPolygon_vertex_mem_sphere n j)


/-- 第１頂点と巡回する隣接頂点を頂点とする、凸包分割のための三角形。 -/
noncomputable def intrinsicPolygonFanTriangle (n : ℕ) (j : Fin (dyadicSides n)) :
    Set EuclideanPlane :=
  convexHull ℝ { (intrinsicRegularPolygon n).vertices ⟨0, dyadicSides_pos n⟩,
    (intrinsicRegularPolygon n).vertices j,
    (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j) }

/-- 分割候補の各三角形はコンパクト、したがって可測である。 -/
theorem intrinsicPolygonFanTriangle_compact (n : ℕ) (j : Fin (dyadicSides n)) :
    IsCompact (intrinsicPolygonFanTriangle n j) := by
  apply Set.Finite.isCompact_convexHull
  exact Set.toFinite _

/-- 分割候補の各三角形は多角形の凸包に含まれる。 -/
theorem intrinsicPolygonFanTriangle_subset_region (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicPolygonFanTriangle n j ⊆ intrinsicPolygonRegion n := by
  unfold intrinsicPolygonFanTriangle intrinsicPolygonRegion
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;>
    exact subset_convexHull ℝ _ ⟨_, rfl⟩

/-- 多角形領域の測度は単位円盤の測度を超えない。 -/
theorem intrinsicPolygonRegion_volume_le_disk (n : ℕ) :
    MeasureTheory.volume (intrinsicPolygonRegion n) ≤
      MeasureTheory.volume (Metric.closedBall (0 : EuclideanPlane) 1) :=
  MeasureTheory.measure_mono (intrinsicPolygonRegion_subset_closedBall n)

/-- 既存の円盤面積公式と解析 bridge による測度上界。 -/
theorem intrinsicPolygonRegion_volume_le_intrinsicPi (n : ℕ) :
    MeasureTheory.volume (intrinsicPolygonRegion n) ≤ ENNReal.ofReal intrinsicPi := by
  have h := intrinsicPolygonRegion_volume_le_disk n
  simpa [intrinsicPi_eq_real_pi] using h

end DkMath.CosmicFormula.Rotation.CF2D
