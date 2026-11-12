/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonMeasure
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicBounds

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonCircumscribed"

/-!
# 原点を中心とする三角形と拡大領域

内接多角形の凸包を `c_(n+1)⁻¹` 倍した集合を定義する。スカラー拡大による
測度の倍率は二次元で `c_(n+1)⁻²` となる。また、原点と隣接頂点から作る
三角形を定義する。これらの定理は、原点ファンの被覆・重なりや、単位円盤が
拡大領域に含まれることを仮定せず、そうした未証明の包含も主張しない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel Filter
open scoped Pointwise Topology

/-- 原点と隣接する二つの頂点の凸包。 -/
noncomputable def intrinsicOriginTriangle (n : ℕ) (j : Fin (dyadicSides n)) : Set EuclideanPlane :=
  convexHull ℝ {0, (intrinsicRegularPolygon n).vertices j,
    (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)}

/-- 原点を共通頂点とする各三角形はコンパクトである。 -/
theorem intrinsicOriginTriangle_compact (n : ℕ) (j : Fin (dyadicSides n)) :
    IsCompact (intrinsicOriginTriangle n j) := by
  exact (Set.toFinite _).isCompact_convexHull ℝ


/-- 隣接頂点の外積は正であり、原点ファンの向きは一貫している。 -/
theorem intrinsicOriginTriangle_vertexCross_pos (n : ℕ) (j : Fin (dyadicSides n)) :
    0 < vertexCross ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)) := by
  rw [intrinsicPolygon_vertexCross]
  exact beam_pos n

/-- 原点ファンの各三角形は測度に関して可測である。 -/
theorem intrinsicOriginTriangle_measurable (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasurableSet (intrinsicOriginTriangle n j) :=
  (intrinsicOriginTriangle_compact n j).isClosed.measurableSet

/-- 原点が多角形領域に属するとき、原点ファンの三角形も領域に含まれる。 -/
theorem intrinsicOriginTriangle_subset_region (n : ℕ) (j : Fin (dyadicSides n))
    (hzero : (0 : EuclideanPlane) ∈ intrinsicPolygonRegion n) :
    intrinsicOriginTriangle n j ⊆ intrinsicPolygonRegion n := by
  unfold intrinsicOriginTriangle
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hzero
  · exact subset_convexHull ℝ _ ⟨_, rfl⟩
  · exact subset_convexHull ℝ _ ⟨_, rfl⟩


/--
原点ファンの測度を加算するための条件付き組立て。

被覆、異なる三角形の測度零の重なり、および各三角形の面積公式は
明示的な仮定であり、この定理自体はそれらを証明しない。
-/
theorem intrinsicPolygonRegion_volume_of_origin_fan (n : ℕ)
    (hcover : intrinsicPolygonRegion n = ⋃ j, intrinsicOriginTriangle n j)
    (hdisjoint : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
      (intrinsicOriginTriangle n)))
    (htriangle : ∀ j : Fin (dyadicSides n),
      MeasureTheory.volume (intrinsicOriginTriangle n j) =
        ENNReal.ofReal ((sequence n).beam / 2)) :
    MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) := by
  rw [hcover, MeasureTheory.measure_iUnion₀ hdisjoint (fun j =>
    (intrinsicOriginTriangle_measurable n j).nullMeasurableSet), tsum_fintype]
  simp_rw [htriangle]
  rw [← ENNReal.ofReal_sum_of_nonneg (by
    intro i hi
    have h := (sequence n).beam_nonneg
    change 0 ≤ (sequence n).beam at h
    positivity)]
  congr 1
  change (∑ _j : Fin (dyadicSides n), (sequence n).beam / 2) = areaApprox n
  rw [Finset.sum_const, Finset.card_fin]
  simp [areaApprox, dyadicSides, pow_succ]
  ring

/-- 内接多角形の凸包を `c_(n+1)⁻¹` 倍した外側の領域候補。 -/
noncomputable def intrinsicPolygonOuterRegion (n : ℕ) : Set EuclideanPlane :=
  ((sequence (n+1)).core)⁻¹ • intrinsicPolygonRegion n

/-- 拡大領域もコンパクトかつ可測である。 -/
theorem intrinsicPolygonOuterRegion_compact (n : ℕ) :
    IsCompact (intrinsicPolygonOuterRegion n) := by
  change IsCompact ((fun x : EuclideanPlane => (sequence (n+1)).core⁻¹ • x) '' intrinsicPolygonRegion n)
  exact (intrinsicPolygonRegion_compact n).image (continuous_id.const_smul ((sequence (n+1)).core⁻¹))

/-- 平面の測度は拡大倍率の二乗で変化する。 -/
theorem intrinsicPolygonOuterRegion_volume (n : ℕ) :
    MeasureTheory.volume (intrinsicPolygonOuterRegion n) =
      ENNReal.ofReal (((sequence (n+1)).core)⁻¹ ^ 2) *
        MeasureTheory.volume (intrinsicPolygonRegion n) := by
  unfold intrinsicPolygonOuterRegion
  rw [MeasureTheory.Measure.addHaar_smul]
  simp only [finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg ((sequence (n+1)).core⁻¹))]


/--
内接領域の測度が `A_n` であることを仮定すると、拡大領域の測度は `U_n` になる。
測度の同一性は仮定であり、領域の被覆や三角形の測度はこの定理では導いていない。
-/
theorem intrinsicPolygonOuterRegion_volume_of_region (n : ℕ)
    (harea : MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n)) :
    MeasureTheory.volume (intrinsicPolygonOuterRegion n) = ENNReal.ofReal (outerApprox n) := by
  rw [intrinsicPolygonOuterRegion_volume, harea, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [outerApprox_eq_areaApprox_div_core_sq]
  ring


/--
内接領域の面積公式と単位円盤の外側領域への包含を仮定した、測度による挟み込み。

両仮定を各段階で証明できれば、円盤の実数値測度が内在的定数に一致する。
この条件付き定理は既存の円周率との同一性を利用しない。
-/
theorem disk_measureReal_eq_intrinsicPi_of_polygon_sandwich
    (harea : ∀ n, MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n))
    (hcover : ∀ n, Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion n) :
    MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) = intrinsicPi := by
  have hlower : ∀ n, areaApprox n ≤ MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) := by
    intro n
    have h := MeasureTheory.measureReal_mono (μ := MeasureTheory.volume)
      (intrinsicPolygonRegion_subset_closedBall n)
      ((isCompact_closedBall (0 : EuclideanPlane) 1).measure_lt_top.ne)
    rw [MeasureTheory.measureReal_def, harea n, ENNReal.toReal_ofReal (areaApprox_nonneg n)] at h
    exact h
  have hupper : ∀ n, MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) ≤ outerApprox n := by
    intro n
    have hfinite : MeasureTheory.volume (intrinsicPolygonOuterRegion n) ≠ ⊤ := by
      rw [intrinsicPolygonOuterRegion_volume_of_region n (harea n)]
      exact ENNReal.ofReal_ne_top
    have h := MeasureTheory.measureReal_mono (μ := MeasureTheory.volume) (hcover n) hfinite
    simp only [MeasureTheory.measureReal_def] at h
    rw [intrinsicPolygonOuterRegion_volume_of_region n (harea n), ENNReal.toReal_ofReal] at h
    · exact h
    · unfold outerApprox
      exact div_nonneg (areaApprox_nonneg (n+1)) (le_of_lt (core_succ_pos n))
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds tendsto_outerApprox_intrinsicPi hupper
  · exact le_of_tendsto_of_tendsto' tendsto_areaApprox_intrinsicPi tendsto_const_nhds hlower

end DkMath.CosmicFormula.Rotation.CF2D
