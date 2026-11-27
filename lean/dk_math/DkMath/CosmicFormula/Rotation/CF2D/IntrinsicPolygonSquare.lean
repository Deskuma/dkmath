/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonFan

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonSquare"

/-!
# 初期正方形の凸包と原点ファン

４頂点を `(1,0), (0,1), (-1,0), (0,-1)` と計算し、４つの辺の
不等式の共通部分を定める。凸性から凸包はその部分に含まれる。
逆に、各象限で標準三角形の係数を明示することにより、この部分は
４枚の原点三角形の和集合に含まれる。これに既存の逆包含を合わせる。
以下の集合等式と測度公式は初期段階 `n=0` に限定される。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel
open scoped InnerProductSpace

namespace Square

/-- 初期段階の４頂点の座標。 -/
theorem vertex_square (j : Fin (dyadicSides 0)) :
    regularVertex (dyadicSides 0) j =
      if j.val = 0 then ⟨1, 0⟩ else if j.val = 1 then ⟨0,1⟩
      else if j.val = 2 then ⟨-1,0⟩ else ⟨0,-1⟩ := by
  change Fin 4 at j
  fin_cases j <;>
    simp [regularVertex, kernelOrbitVertex, regularKernel_dyadic, QuadrantUnitKernel.sequence,
      QuadrantUnitKernel.initial, UnitKernel.act, UnitKernel.mul_eq_star, UnitKernel.star, UnitKernel.one, Vec.star, Vec.one,
      pow_succ]

/-- 回転した正方形を定める４つの辺の不等式。 -/
def diamond : Set EuclideanPlane := {x | x 0 + x 1 ≤ 1 ∧ x 0 - x 1 ≤ 1 ∧ -x 0 + x 1 ≤ 1 ∧ -x 0 - x 1 ≤ 1}

/-- ４つの半平面の共通部分は凸である。 -/
theorem diamond_convex : Convex ℝ diamond := by
  intro x hx y hy a b ha hb hab
  simp only [diamond, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1), mul_nonneg hb (sub_nonneg.mpr hy.1),
      mul_nonneg ha (sub_nonneg.mpr hx.2.1), mul_nonneg hb (sub_nonneg.mpr hy.2.1),
      mul_nonneg ha (sub_nonneg.mpr hx.2.2.1), mul_nonneg hb (sub_nonneg.mpr hy.2.2.1),
      mul_nonneg ha (sub_nonneg.mpr hx.2.2.2), mul_nonneg hb (sub_nonneg.mpr hy.2.2.2)]

/-- ４頂点が全て半平面の共通部分にあるので、その凸包も含まれる。 -/
theorem region_subset_diamond : intrinsicPolygonRegion 0 ⊆ diamond := by
  apply convexHull_min _ diamond_convex
  rintro _ ⟨j, rfl⟩
  change pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides 0) j)) ∈ diamond
  rw [vertex_square j]
  change Fin 4 at j
  fin_cases j <;> norm_num [diamond, pairToEuclideanPlane, Vec.toProd]

private theorem v0 : (intrinsicRegularPolygon 0).vertices ⟨0, by norm_num [dyadicSides]⟩ = pairToEuclideanPlane (1,0) := by
  change pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides 0) _)) = _
  rw [vertex_square]
  rfl

private theorem v1 : (intrinsicRegularPolygon 0).vertices ⟨1, by norm_num [dyadicSides]⟩ = pairToEuclideanPlane (0,1) := by
  change pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides 0) _)) = _
  rw [vertex_square]
  rfl

private theorem v2 : (intrinsicRegularPolygon 0).vertices ⟨2, by norm_num [dyadicSides]⟩ = pairToEuclideanPlane (-1,0) := by
  change pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides 0) _)) = _
  rw [vertex_square]
  rfl

private theorem v3 : (intrinsicRegularPolygon 0).vertices ⟨3, by norm_num [dyadicSides]⟩ = pairToEuclideanPlane (0,-1) := by
  change pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides 0) _)) = _
  rw [vertex_square]
  rfl

/-- 半平面の共通部分の点は象限に応じた原点三角形に属する。 -/
theorem diamond_subset_fan : diamond ⊆ intrinsicOriginFan 0 := by
  intro x hx
  have h := hx
  change x 0 + x 1 ≤ 1 ∧ x 0 - x 1 ≤ 1 ∧ -x 0 + x 1 ≤ 1 ∧ -x 0 - x 1 ≤ 1 at h
  rw [intrinsicOriginFan, Set.mem_iUnion]
  by_cases hx0 : 0 ≤ x 0
  · by_cases hx1 : 0 ≤ x 1
    · refine ⟨⟨0, by norm_num [dyadicSides]⟩, ?_⟩
      rw [← originTriangleLinearMap_image]
      refine ⟨![x 0, x 1], ?_, ?_⟩
      · rw [mem_standardTriangle_iff]
        simpa using ⟨hx0, hx1, h.1⟩
      · change x 0 • ((intrinsicRegularPolygon 0).vertices ⟨0, by norm_num [dyadicSides]⟩) +
          x 1 • ((intrinsicRegularPolygon 0).vertices ⟨1, by norm_num [dyadicSides]⟩) = x
        rw [v0, v1]
        ext i
        fin_cases i <;> simp [pairToEuclideanPlane]
    · refine ⟨⟨3, by norm_num [dyadicSides]⟩, ?_⟩
      rw [← originTriangleLinearMap_image]
      refine ⟨![-x 1, x 0], ?_, ?_⟩
      · rw [mem_standardTriangle_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        constructor <;> [linarith; constructor <;> linarith [h.2.1]]
      · change (-x 1) • ((intrinsicRegularPolygon 0).vertices ⟨3, by norm_num [dyadicSides]⟩) +
          x 0 • ((intrinsicRegularPolygon 0).vertices ⟨0, by norm_num [dyadicSides]⟩) = x
        rw [v3, v0]
        ext i
        fin_cases i <;> simp [pairToEuclideanPlane]
  · by_cases hx1 : 0 ≤ x 1
    · refine ⟨⟨1, by norm_num [dyadicSides]⟩, ?_⟩
      rw [← originTriangleLinearMap_image]
      refine ⟨![x 1, -x 0], ?_, ?_⟩
      · rw [mem_standardTriangle_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        constructor <;> [linarith; constructor <;> linarith [h.2.2.1]]
      · change x 1 • ((intrinsicRegularPolygon 0).vertices ⟨1, by norm_num [dyadicSides]⟩) +
          (-x 0) • ((intrinsicRegularPolygon 0).vertices ⟨2, by norm_num [dyadicSides]⟩) = x
        rw [v1, v2]
        ext i
        fin_cases i <;> simp [pairToEuclideanPlane]
    · refine ⟨⟨2, by norm_num [dyadicSides]⟩, ?_⟩
      rw [← originTriangleLinearMap_image]
      refine ⟨![-x 0, -x 1], ?_, ?_⟩
      · rw [mem_standardTriangle_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        constructor <;> [linarith; constructor <;> linarith [h.2.2.2]]
      · change (-x 0) • ((intrinsicRegularPolygon 0).vertices ⟨2, by norm_num [dyadicSides]⟩) +
          (-x 1) • ((intrinsicRegularPolygon 0).vertices ⟨3, by norm_num [dyadicSides]⟩) = x
        rw [v2, v3]
        ext i
        fin_cases i <;> simp [pairToEuclideanPlane]



/-- 初期段階では、４辺の半平面の共通部分は４辺の不等式で定めた集合に等しい。 -/
theorem edgeHalfSpaces_zero_eq_diamond : intrinsicEdgeHalfSpaces 0 = diamond := by
  ext x
  have hc : (sequence 1).core ^ 2 = (1 / 2 : ℝ) := by
    simpa [QuadrantUnitKernel.sequence, initial, core] using core_succ_sq 0
  change (∀ j : Fin (dyadicSides 0),
    ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices j)
      ((intrinsicRegularPolygon 0).vertices (regularVertexNext (dyadicSides_pos 0) j)), x⟫_ℝ ≤
        (sequence 1).core ^ 2) ↔ x ∈ diamond
  rw [hc]
  have hi0 : ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨0, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices (regularVertexNext (dyadicSides_pos 0) ⟨0, by norm_num [dyadicSides]⟩)), x⟫_ℝ = (x 0+x 1)/2 := by
    change ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨0, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices ⟨1, by norm_num [dyadicSides]⟩), x⟫_ℝ = _
    rw [v0, v1, midpoint_eq_smul_add]
    simp [PiLp.inner_apply, Fin.sum_univ_two, pairToEuclideanPlane]
    ring
  have hi1 : ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨1, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices (regularVertexNext (dyadicSides_pos 0) ⟨1, by norm_num [dyadicSides]⟩)), x⟫_ℝ = (-x 0+x 1)/2 := by
    change ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨1, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices ⟨2, by norm_num [dyadicSides]⟩), x⟫_ℝ = _
    rw [v1, v2, midpoint_eq_smul_add]
    simp [PiLp.inner_apply, Fin.sum_univ_two, pairToEuclideanPlane]
    ring
  have hi2 : ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨2, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices (regularVertexNext (dyadicSides_pos 0) ⟨2, by norm_num [dyadicSides]⟩)), x⟫_ℝ = (-x 0-x 1)/2 := by
    change ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨2, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices ⟨3, by norm_num [dyadicSides]⟩), x⟫_ℝ = _
    rw [v2, v3, midpoint_eq_smul_add]
    simp [PiLp.inner_apply, Fin.sum_univ_two, pairToEuclideanPlane]
    ring
  have hi3 : ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨3, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices (regularVertexNext (dyadicSides_pos 0) ⟨3, by norm_num [dyadicSides]⟩)), x⟫_ℝ = (x 0-x 1)/2 := by
    change ⟪midpoint ℝ ((intrinsicRegularPolygon 0).vertices ⟨3, by norm_num [dyadicSides]⟩)
      ((intrinsicRegularPolygon 0).vertices ⟨0, by norm_num [dyadicSides]⟩), x⟫_ℝ = _
    rw [v3, v0, midpoint_eq_smul_add]
    simp [PiLp.inner_apply, Fin.sum_univ_two, pairToEuclideanPlane]
    ring
  constructor
  · intro h
    have h0 := h ⟨0, by norm_num [dyadicSides]⟩
    have h1 := h ⟨1, by norm_num [dyadicSides]⟩
    have h2 := h ⟨2, by norm_num [dyadicSides]⟩
    have h3 := h ⟨3, by norm_num [dyadicSides]⟩
    rw [hi0] at h0
    rw [hi1] at h1
    rw [hi2] at h2
    rw [hi3] at h3
    change x 0+x 1 ≤ 1 ∧ x 0-x 1 ≤ 1 ∧ -x 0+x 1 ≤ 1 ∧ -x 0-x 1 ≤ 1
    constructor <;> [linarith; constructor <;> [linarith; constructor <;> linarith]]
  · intro h j
    change x 0+x 1 ≤ 1 ∧ x 0-x 1 ≤ 1 ∧ -x 0+x 1 ≤ 1 ∧ -x 0-x 1 ≤ 1 at h
    change Fin 4 at j
    fin_cases j <;> dsimp only <;> simp only [dyadicSides] at *
    · rw [hi0]; linarith [h.1]
    · rw [hi1]; linarith [h.2.2.1]
    · rw [hi2]; linarith [h.2.2.2]
    · rw [hi3]; linarith [h.2.1]

end Square

/-- 初期正方形の凸包は４枚の原点三角形でちょうど覆われる。 -/
theorem intrinsicPolygonRegion_zero_eq_originFan : intrinsicPolygonRegion 0 = intrinsicOriginFan 0 :=
  Set.Subset.antisymm (Square.region_subset_diamond.trans Square.diamond_subset_fan)
    (intrinsicOriginFan_subset_region 0)

/-- 初期正方形の凸包の測度は 2 である。 -/
theorem intrinsicPolygonRegion_zero_volume :
    MeasureTheory.volume (intrinsicPolygonRegion 0) = ENNReal.ofReal 2 := by
  rw [intrinsicPolygonRegion_zero_eq_originFan, intrinsicOriginFan_zero_volume]


/-- 初期凸包は４辺の不等式で表される正方形に等しい。 -/
theorem intrinsicPolygonRegion_zero_eq_diamond : intrinsicPolygonRegion 0 = Square.diamond :=
  Set.Subset.antisymm Square.region_subset_diamond
    (Square.diamond_subset_fan.trans (intrinsicOriginFan_subset_region 0))

/-- ４辺の不等式は `|x| + |y| ≤ 1` と同値である。 -/
theorem square_diamond_iff (x : EuclideanPlane) : x ∈ Square.diamond ↔ |x 0| + |x 1| ≤ 1 := by
  change (x 0 + x 1 ≤ 1 ∧ x 0 - x 1 ≤ 1 ∧ -x 0 + x 1 ≤ 1 ∧ -x 0 - x 1 ≤ 1) ↔ _
  rcases le_total 0 (x 0) with h0 | h0 <;> rcases le_total 0 (x 1) with h1 | h1
  · rw [abs_of_nonneg h0, abs_of_nonneg h1]
    constructor
    · rintro ⟨h, _, _, _⟩; exact h
    · intro h; exact ⟨h, by linarith, by linarith, by linarith⟩
  · rw [abs_of_nonneg h0, abs_of_nonpos h1]
    constructor
    · rintro ⟨_, h, _, _⟩; linarith
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [abs_of_nonpos h0, abs_of_nonneg h1]
    constructor
    · rintro ⟨_, _, h, _⟩; exact h
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [abs_of_nonpos h0, abs_of_nonpos h1]
    constructor
    · rintro ⟨_, _, _, h⟩; exact h
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- 初期核の半分の core を半径とする閉円盤は正方形の凸包に含まれる。 -/
theorem intrinsicPolygonRegion_zero_innerBall_subset : Metric.closedBall (0 : EuclideanPlane) (sequence 1).core ⊆ intrinsicPolygonRegion 0 := by
  intro x hx
  rw [intrinsicPolygonRegion_zero_eq_diamond, square_diamond_iff]
  have hx' : ‖x‖ ≤ (sequence 1).core := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hp := core_succ_pos 0
  have hs := core_succ_sq 0
  have hs' : (sequence 1).core ^ 2 = (1 / 2 : ℝ) := by
    simpa [QuadrantUnitKernel.sequence, initial, core] using hs
  have hnorm : ‖x‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    have h := sq_le_sq₀ (norm_nonneg x) (le_of_lt hp) |>.2 hx'
    linarith
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hnorm
  have habs : (|x 0| + |x 1|) ^ 2 ≤ 2 * ((x 0) ^ 2 + (x 1) ^ 2) := by
    nlinarith [sq_nonneg (|x 0| - |x 1|), sq_abs (x 0), sq_abs (x 1)]
  have hnon : 0 ≤ |x 0| + |x 1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

/-- 初期正方形を半径で拡大した領域は単位閉円盤を含む。 -/
theorem closedBall_subset_intrinsicPolygonOuterRegion_zero :
    Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion 0 :=
  closedBall_subset_outerRegion_of_innerBall_subset 0 intrinsicPolygonRegion_zero_innerBall_subset


/-- 初期正方形の凸包は、４辺の内側の支持半平面の共通部分に等しい。 -/
theorem intrinsicPolygonRegion_zero_eq_edgeHalfSpaces :
    intrinsicPolygonRegion 0 = intrinsicEdgeHalfSpaces 0 := by
  rw [Square.edgeHalfSpaces_zero_eq_diamond, intrinsicPolygonRegion_zero_eq_diamond]

end DkMath.CosmicFormula.Rotation.CF2D
