/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonSupport
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicStandardTriangleMeasure
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonSquare

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicRefinementCapMeasure"

/-! # 二分化で追加される三角形の測度 -/

namespace DkMath.CosmicFormula.Rotation.CF2D
open MeasureTheory QuadrantUnitKernel

/-- 行列式による三角形の測度公式を既存の外積の記法で表す。 -/
theorem triangle_volume_eq_abs_cross (p w q : EuclideanPlane) :
    volume (convexHull ℝ {p, w, q}) =
      ENNReal.ofReal (|vertexCross (w - p) (q - p)| / 2) :=
  euclideanTriangle_volume_eq_abs_det p w q

set_option backward.isDefEq.respectTransparency false in
/-- 二分化で追加する三角形の二辺の行列式。二つの新辺の外積の和から旧辺の外積を引く。 -/
theorem refinementCap_cross (n : ℕ) (j : Fin (dyadicSides n)) :
    let p := (intrinsicRegularPolygon n).vertices j
    let w := (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n j)
    let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
    vertexCross (w - p) (q - p) = 2 * (sequence (n + 1)).beam - (sequence n).beam := by
  dsimp only
  have h₁ := intrinsicPolygon_vertexCross (n + 1) (evenIndex n j)
  have h₂ := intrinsicPolygon_vertexCross (n + 1) (oddIndex n j)
  change vertexCross _ ((intrinsicRegularPolygon (n + 1)).vertices
    (directVertexNext (n + 1) (evenIndex n j))) = _ at h₁
  change vertexCross _ ((intrinsicRegularPolygon (n + 1)).vertices
    (directVertexNext (n + 1) (oddIndex n j))) = _ at h₂
  rw [directVertexNext_even, intrinsicRegularPolygon_even_vertex n j] at h₁
  rw [directVertexNext_odd] at h₂
  change vertexCross _ ((intrinsicRegularPolygon (n + 1)).vertices
    (evenIndex n (regularVertexNext (dyadicSides_pos n) j))) = _ at h₂
  rw [intrinsicRegularPolygon_even_vertex] at h₂
  have h₀ := intrinsicPolygon_vertexCross n j
  simp only [vertexCross, PiLp.sub_apply] at *
  linarith only [h₀, h₁, h₂]

/-- 各増分三角形の測度は s_(n+1) − s_n/2 である。行列式 2s_(n+1) − s_n は、倍角関係で 2(1 − c_(n+1))s_(n+1) と書けるので正である。三角形の行列式公式により、その半分が測度になる。 -/
theorem refinementCap_volume (n : ℕ) (j : Fin (dyadicSides n)) :
    volume (refinementCap n j) =
      ENNReal.ofReal ((sequence (n + 1)).beam - (sequence n).beam / 2) := by
  unfold refinementCap
  rw [triangle_volume_eq_abs_cross, refinementCap_cross, abs_of_pos]
  · congr 1
    ring
  · rw [refinement_beam n]
    nlinarith [mul_pos (sub_pos.mpr (core_lt_one (n + 1))) (beam_pos (n + 1))]

/-- 増分三角形の個別測度の総和は A_(n+1) − A_n に等しい。三角形の個数 4·2^n を共通の測度に掛けると得られる。和集合の測度への読み替えには、別途、測度零の交わりが必要である。 -/
theorem refinementCaps_sum_volume (n : ℕ) :
    (∑ j : Fin (dyadicSides n), volume (refinementCap n j)) =
      ENNReal.ofReal (areaApprox (n + 1) - areaApprox n) := by
  simp only [refinementCap_volume, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  simp only [dyadicSides, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, areaApprox, pow_succ]
  ring

/-- 被覆と測度零の交わりが得られれば、旧領域の測度に増分を足せる。 -/
theorem intrinsicPolygonRegion_volume_succ_of_caps (n : ℕ)
    (hcover : intrinsicPolygonRegion (n + 1) =
      intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j))
    (hpair : Pairwise (Function.onFun (AEDisjoint volume) (refinementCap n)))
    (hold : AEDisjoint volume (intrinsicPolygonRegion n) (⋃ j, refinementCap n j)) :
    volume (intrinsicPolygonRegion (n + 1)) =
      volume (intrinsicPolygonRegion n) + ENNReal.ofReal (areaApprox (n + 1) - areaApprox n) := by
  rw [hcover, measure_union₀' (intrinsicPolygonRegion_measurable n).nullMeasurableSet hold,
    measure_iUnion₀ hpair, tsum_fintype, refinementCaps_sum_volume]
  intro j
  exact ((Set.toFinite _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet

/-- 各段階で増分分割が成立すれば、正方形からの帰納法で凸包の測度を計算できる。 -/
theorem intrinsicPolygonRegion_volume_of_cap_decomposition
    (hcover : ∀ n, intrinsicPolygonRegion (n + 1) =
      intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j))
    (hpair : ∀ n, Pairwise (Function.onFun (AEDisjoint volume) (refinementCap n)))
    (hold : ∀ n, AEDisjoint volume (intrinsicPolygonRegion n) (⋃ j, refinementCap n j))
    (n : ℕ) : volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) := by
  induction n with
  | zero => rw [intrinsicPolygonRegion_zero_volume, areaApprox_zero]
  | succ n ih =>
    rw [intrinsicPolygonRegion_volume_succ_of_caps n (hcover n) (hpair n) (hold n), ih,
      ← ENNReal.ofReal_add (areaApprox_nonneg n)
        (sub_nonneg.mpr (areaApprox_monotone (Nat.le_succ n)))]
    congr 1
    ring

/-- 支持直線による分離を使うと、面積の帰納法に必要なのは被覆と増分三角形同士の零交差である。 -/
theorem intrinsicPolygonRegion_volume_of_cap_cover_and_pairwise
    (hcover : ∀ n, intrinsicPolygonRegion (n + 1) =
      intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j))
    (hpair : ∀ n, Pairwise (Function.onFun (AEDisjoint volume) (refinementCap n)))
    (n : ℕ) : volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_cap_decomposition hcover hpair refinementCaps_aedisjoint_old_region n

/-- 増分三角形の被覆が各段階で成立すれば、凸包の測度は面積候補に一致する。
加法性に必要な零交差は各旧辺の支持直線から従う。 -/
theorem intrinsicPolygonRegion_volume_of_cap_cover
    (hcover : ∀ n, intrinsicPolygonRegion (n + 1) =
      intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j))
    (n : ℕ) : volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_cap_cover_and_pairwise hcover refinementCaps_pairwise_aedisjoint n

/-- 各段階の凸包の測度は、代数的な面積候補 A_n に等しい。初期正方形の測度は 2。細分化による集合分割と測度零の交わりにより、次の段階では A_(n+1) − A_n が加わる。 -/
theorem intrinsicPolygonRegion_volume_eq_areaApprox (n : ℕ) :
    volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_cap_cover intrinsicPolygon_refinement_caps n

/-- 単位閉円盤の実数値測度は内在的な円周率に等しい。

内接凸包の測度 A_n と外接領域の測度 U_n は、円盤の測度を上下から挟み、どちらも intrinsicPi に収束する。この導出は intrinsicPi_eq_real_pi を使わない。円盤包含を得る支持半平面の幾何証明は標準角度と三角関数を使う。 -/
theorem disk_measureReal_eq_intrinsicPi :
    volume.real (Metric.closedBall (0 : EuclideanPlane) 1) = intrinsicPi :=
  disk_measureReal_eq_intrinsicPi_of_polygon_sandwich
    intrinsicPolygonRegion_volume_eq_areaApprox closedBall_subset_intrinsicPolygonOuterRegion

end DkMath.CosmicFormula.Rotation.CF2D
