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

/-- 三角形の測度は、一頂点を原点へ移した二辺の行列式の絶対値の半分。 -/
theorem triangle_volume_eq_abs_cross (p w q : EuclideanPlane) :
    volume (convexHull ℝ {p, w, q}) =
      ENNReal.ofReal (|vertexCross (w - p) (q - p)| / 2) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(w - p) 0, (q - p) 0; (w - p) 1, (q - p) 1]
  let f := Matrix.toLin' M
  let a := WithLp.ofLp p
  let g : (Fin 2 → ℝ) →ᵃ[ℝ] (Fin 2 → ℝ) :=
    AffineMap.mk' (fun x => f x + a) f 0 (by simp)
  let L := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap
  have hf0 : g 0 = a := by change f 0 + a = a; simp
  have hf1 : g (Pi.single 0 1) = WithLp.ofLp w := by
    funext i
    fin_cases i <;> change (Matrix.mulVec M (Pi.single 0 1) + a) _ = _ <;>
      simp [M, a]
  have hf2 : g (Pi.single 1 1) = WithLp.ofLp q := by
    funext i
    fin_cases i <;> change (Matrix.mulVec M (Pi.single 1 1) + a) _ = _ <;>
      simp [M, a]
  have hi : g '' standardTriangle = convexHull ℝ {a, WithLp.ofLp w, WithLp.ofLp q} := by
    rw [standardTriangle, AffineMap.image_convexHull]
    simp [hf0, hf1, hf2]
  have hpre : (WithLp.ofLp : EuclideanPlane → (Fin 2 → ℝ)) ⁻¹' (g '' standardTriangle) =
      convexHull ℝ {p, w, q} := by
    have he : L '' convexHull ℝ {p, w, q} = g '' standardTriangle := by
      rw [L.image_convexHull, hi]
      simp [L, a]
    rw [← he]
    exact Set.preimage_image_eq _ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).injective
  have hc : IsCompact (f '' standardTriangle) :=
    ((Set.toFinite _).isCompact_convexHull ℝ).image
      (LinearMap.continuous_of_finiteDimensional f)
  have htrans : (fun x : Fin 2 → ℝ => x - a) ⁻¹' (f '' standardTriangle) =
      g '' standardTriangle := by
    ext y
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, eq_sub_iff_add_eq.mp he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by change f x = f x + a - a; simp⟩
  have hm := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (s := g '' standardTriangle) (by rw [hi]; exact ((Set.toFinite _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet)
  rw [hpre] at hm
  rw [hm, ← htrans]
  -- 平行移動は測度を保ち、線形部分の測度倍率は行列式の絶対値である。
  have ht' : volume ((fun x : Fin 2 → ℝ => x - a) ⁻¹' (f '' standardTriangle)) =
      volume (f '' standardTriangle) :=
    by
      have h := (volume.measurePreserving_sub_left (-a)).comp
        (volume.measurePreserving_sub_left (0 : Fin 2 → ℝ))
      have he : (fun x : Fin 2 → ℝ => -a - (0 - x)) = fun x => x - a := by
        funext x
        abel
      change MeasurePreserving (fun x : Fin 2 → ℝ => -a - (0 - x)) volume volume at h
      rw [he] at h
      exact h.measure_preimage hc.isClosed.measurableSet.nullMeasurableSet
  rw [ht', Measure.addHaar_image_linearMap, standardTriangle_volume]
  have hd : LinearMap.det f = vertexCross (w - p) (q - p) := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 2))]
    simp [f, M, Matrix.det_fin_two, vertexCross, mul_comm]
  rw [hd, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

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

/-- 各増分三角形の測度は半角核の beam から旧 beam の半分を引いた値。 -/
theorem refinementCap_volume (n : ℕ) (j : Fin (dyadicSides n)) :
    volume (refinementCap n j) =
      ENNReal.ofReal ((sequence (n + 1)).beam - (sequence n).beam / 2) := by
  unfold refinementCap
  rw [triangle_volume_eq_abs_cross, refinementCap_cross, abs_of_pos]
  · congr 1
    ring
  · rw [refinement_beam n]
    nlinarith [mul_pos (sub_pos.mpr (core_lt_one (n + 1))) (beam_pos (n + 1))]

/-- 個々の測度の総和は面積候補の一段分の差に一致する。 -/
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

/-- 二分化で得る内接多角形の凸包の測度は、代数的な面積候補に等しい。 -/
theorem intrinsicPolygonRegion_volume_eq_areaApprox (n : ℕ) :
    volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_cap_cover intrinsicPolygon_refinement_caps n

/-- 内接・外接多角形の測度で挟むと、単位閉円盤の実数値測度は内在的な円周率に一致する。 -/
theorem disk_measureReal_eq_intrinsicPi :
    volume.real (Metric.closedBall (0 : EuclideanPlane) 1) = intrinsicPi :=
  disk_measureReal_eq_intrinsicPi_of_polygon_sandwich
    intrinsicPolygonRegion_volume_eq_areaApprox closedBall_subset_intrinsicPolygonOuterRegion

end DkMath.CosmicFormula.Rotation.CF2D
