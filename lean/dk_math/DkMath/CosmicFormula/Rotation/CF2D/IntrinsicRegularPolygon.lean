/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPiBridge
import DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit
import Mathlib.Geometry.Polygon.Basic

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicRegularPolygon"

/-!
# 二分核と正多角形の頂点

内在的な二分核を、既存の等角有限軌道の生成核と照合する。軌道を
ユークリッド平面の `Polygon` として取り出し、その頂点が単位円上にあり、
重複せず、等角回転で順に移ることを示す。頂点の座標から作る有向面積和も
計算する。測度としての凸包の面積との一致は別途必要である。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel

local instance : Fact (Module.finrank ℝ EuclideanPlane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- 第 `n` 段階に対応する辺数 `4·2^n`。 -/
def dyadicSides (n : ℕ) : ℕ := 4 * 2 ^ n

/-- 対応する辺数は正である。 -/
theorem dyadicSides_pos (n : ℕ) : 0 < dyadicSides n := by
  unfold dyadicSides
  positivity

/-- 正多角形の一辺に対応する回転角は、二分核の比較角に等しい。 -/
theorem regularStepAngle_dyadic (n : ℕ) :
    normalizedPhaseAngle (regularPhaseStep (dyadicSides n)) = dyadicAngle n := by
  rw [regularStepAngle_eq_two_pi_div]
  simp only [dyadicSides, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, dyadicAngle, pow_succ]
  ring

/-- 等角有限軌道の生成核は、内在的に作った第 `n` 二分核である。 -/
theorem regularKernel_dyadic (n : ℕ) :
    regularKernel (dyadicSides n) = (sequence n).kernel := by
  apply UnitKernel.ext
  change (realTrigKernelFamily.kernel (normalizedPhaseAngle (regularPhaseStep (dyadicSides n)))).val = _
  rw [regularStepAngle_dyadic]
  have h := sequence_trig n
  cases hv : (sequence n).kernel.val with
  | mk c s =>
    simp only [core, beam, hv] at h
    simp [realTrigKernelFamily, h.1.symm, h.2.symm]

/-- 二分核が生成する単位円上の有限軌道をユークリッド平面の多角形にする。 -/
noncomputable def intrinsicRegularPolygon (n : ℕ) : Polygon EuclideanPlane (dyadicSides n) :=
  ⟨euclideanRegularVertex (dyadicSides n)⟩

/-- 多角形の各頂点は単位円上にある。 -/
theorem intrinsicRegularPolygon_vertex_mem_sphere (n : ℕ) (j : Fin (dyadicSides n)) :
    (intrinsicRegularPolygon n).vertices j ∈ Metric.sphere (0 : EuclideanPlane) 1 :=
  euclideanRegularVertex_mem_unitSphere _ _

/-- 多角形の頂点は互いに異なる。 -/
theorem intrinsicRegularPolygon_vertices_injective (n : ℕ) :
    Function.Injective (intrinsicRegularPolygon n).vertices :=
  euclideanRegularVertex_injective (dyadicSides_pos n)

/-- 次の頂点は一辺分の角度だけ回転した頂点である。 -/
theorem intrinsicRegularPolygon_vertex_next (n : ℕ) (j : Fin (dyadicSides n)) :
    (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j) =
      euclideanPlaneOrientation.rotation (dyadicAngle n) ((intrinsicRegularPolygon n).vertices j) := by
  simpa [intrinsicRegularPolygon, ← regularStepAngle_dyadic n] using
    euclideanRegularVertex_next (dyadicSides_pos n) j


/-- 二頂点と原点が作る有向三角形の面積の２倍。 -/
def vertexCross (p q : EuclideanPlane) : ℝ := p 0 * q 1 - p 1 * q 0

/-- 軌道多角形の頂点を巡回して作る靴紐公式の符号付き面積。 -/
noncomputable def intrinsicPolygonSignedArea (n : ℕ) : ℝ :=
  (∑ j : Fin (dyadicSides n), vertexCross ((intrinsicRegularPolygon n).vertices j)
    ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))) / 2

/-- 各辺に対する外積は核の beam 座標と等しい。 -/
theorem intrinsicPolygon_vertexCross (n : ℕ) (j : Fin (dyadicSides n)) :
    vertexCross ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)) =
      (sequence n).beam := by
  have hv := regularVertex_next (dyadicSides_pos n) j
  rw [regularKernel_dyadic n] at hv
  have hq := regularVertex_q2 (dyadicSides n) j
  simp only [Vec.q2] at hq
  unfold vertexCross intrinsicRegularPolygon euclideanRegularVertex
  simp only [hv, UnitKernel.act, Vec.star, Vec.toProd, pairToEuclideanPlane]
  change (regularVertex (dyadicSides n) j).core *
      ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).beam +
       (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).core) -
    (regularVertex (dyadicSides n) j).beam *
      ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).core -
       (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).beam) = _
  change _ = (sequence n).kernel.val.beam
  calc
    _ = (sequence n).kernel.val.beam * ((regularVertex (dyadicSides n) j).core ^ 2 +
        (regularVertex (dyadicSides n) j).beam ^ 2) := by ring
    _ = _ := by rw [hq, mul_one]

/-- 頂点の靴紐和は代数的な面積候補 `A_n` に等しい。 -/
theorem intrinsicPolygonSignedArea_eq_areaApprox (n : ℕ) :
    intrinsicPolygonSignedArea n = areaApprox n := by
  unfold intrinsicPolygonSignedArea
  simp only [intrinsicPolygon_vertexCross, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  simp only [dyadicSides, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, areaApprox, pow_succ]
  ring


/-- 多角形の辺の長さの和で定めたユークリッド周長。 -/
noncomputable def intrinsicPolygonPerimeter (n : ℕ) : ℝ :=
  ∑ j : Fin (dyadicSides n), dist ((intrinsicRegularPolygon n).vertices j)
    ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))

/-- 各辺の長さは `√(2-2c_n)` である。 -/
theorem intrinsicPolygon_edge_length (n : ℕ) (j : Fin (dyadicSides n)) :
    dist ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)) =
      Real.sqrt (2 - 2 * (sequence n).core) := by
  have hv := regularVertex_next (dyadicSides_pos n) j
  rw [regularKernel_dyadic n] at hv
  have hq := regularVertex_q2 (dyadicSides n) j
  simp only [Vec.q2] at hq
  have hk := (sequence n).norm
  have hc := (sequence n).core_le_one
  apply (sq_eq_sq₀ (dist_nonneg) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by linarith)]
  rw [dist_eq_norm]
  unfold intrinsicRegularPolygon euclideanRegularVertex
  dsimp only
  rw [hv]
  have hsub : pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides n) j)) -
      pairToEuclideanPlane (Vec.toProd ((sequence n).kernel.act (regularVertex (dyadicSides n) j))) =
      pairToEuclideanPlane
        ((regularVertex (dyadicSides n) j).core - ((sequence n).kernel.act (regularVertex (dyadicSides n) j)).core,
         (regularVertex (dyadicSides n) j).beam - ((sequence n).kernel.act (regularVertex (dyadicSides n) j)).beam) := by
    ext i
    fin_cases i <;> simp [pairToEuclideanPlane, Vec.toProd]
  rw [hsub, pairToEuclideanPlane_norm_sq]
  simp only [UnitKernel.act_core, UnitKernel.act_beam]
  change _ = 2 - 2 * (sequence n).kernel.val.core
  change (sequence n).kernel.val.core ^ 2 + (sequence n).kernel.val.beam ^ 2 = 1 at hk
  have hid : ((regularVertex (dyadicSides n) j).core -
        ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).core -
         (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).beam)) ^ 2 +
      ((regularVertex (dyadicSides n) j).beam -
        ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).beam +
         (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).core)) ^ 2 =
      ((1 - (sequence n).kernel.val.core) ^ 2 + (sequence n).kernel.val.beam ^ 2) *
      ((regularVertex (dyadicSides n) j).core ^ 2 + (regularVertex (dyadicSides n) j).beam ^ 2) := by ring
  rw [hid, hq, mul_one]
  nlinarith [hk]

/-- ユークリッド周長の半分は代数的な半周長候補 `P_n` に等しい。 -/
theorem intrinsicPolygonPerimeter_div_two (n : ℕ) :
    intrinsicPolygonPerimeter n / 2 = halfPerimeterApprox n := by
  unfold intrinsicPolygonPerimeter
  simp only [intrinsicPolygon_edge_length, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  simp only [dyadicSides, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, halfPerimeterApprox, pow_succ]
  ring

end DkMath.CosmicFormula.Rotation.CF2D
