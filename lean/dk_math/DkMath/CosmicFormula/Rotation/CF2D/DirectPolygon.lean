/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DyadicConeSupport
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

#print "file: DkMath.CosmicFormula.Rotation.CF2D.DirectPolygon"

/-! # 直接軌道の凸包と支持半平面 -/

namespace DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel

/-- 二分核の直接軌道を頂点集合とする凸包。 -/
noncomputable def directPolygonRegion (n : ℕ) : Set (ℝ × ℝ) :=
  convexHull ℝ (Set.range (orbitPair n))

/-- 旧辺の中点を法線とする線形汎関数。座標平面で内積を取る。 -/
noncomputable def directEdgeFunctional (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  let m := refinementMidpoint (directVertex n j) (directVertex n (directVertexNext n j))
  m.core • LinearMap.fst ℝ ℝ ℝ + m.beam • LinearMap.snd ℝ ℝ ℝ

/-- 直接軌道のすべての辺が定める内側半平面の共通部分。 -/
def directEdgeHalfSpaces (n : ℕ) : Set (ℝ × ℝ) :=
  {x | ∀ j, directEdgeFunctional n j x ≤ (sequence (n + 1)).core ^ 2}

private theorem edge_apply (n : ℕ) (j : Fin (4 * 2 ^ n)) (x : Vec ℝ) :
    directEdgeFunctional n j (x.core, x.beam) =
      refinementDot (refinementMidpoint (directVertex n j)
        (directVertex n (directVertexNext n j))) x := by
  simp [directEdgeFunctional, refinementDot, smul_eq_mul]

/-- 原点は反対向きの二頂点の中点である。 -/
theorem directPolygonRegion_origin_mem (n : ℕ) : 0 ∈ directPolygonRegion n := by
  let j : Fin (4 * 2 ^ n) := ⟨0, by positivity⟩
  have h₁ : orbitPair n j ∈ directPolygonRegion n := subset_convexHull ℝ _ ⟨j, rfl⟩
  have h₂ : orbitPair n (directVertexOpposite n j) ∈ directPolygonRegion n :=
    subset_convexHull ℝ _ ⟨_, rfl⟩
  have hneg : orbitPair n (directVertexOpposite n j) = -orbitPair n j := by
    unfold orbitPair
    rw [directVertex_opposite]
    rfl
  rw [hneg] at h₂
  have hm := (convex_convexHull ℝ (Set.range (orbitPair n))).midpoint_mem h₁ h₂
  rwa [midpoint_eq_smul_add, add_neg_cancel, smul_zero] at hm

/-- 直接軌道の凸包と全辺の内側半平面の共通部分は一致する。
順方向では保存量による頂点の支持不等式を凸包に延ばす。
逆方向では非負錐の被覆から係数を選び、半平面条件で係数の和を 1 以下に抑える。 -/
theorem directPolygonRegion_eq_edgeHalfSpaces (n : ℕ) :
    directPolygonRegion n = directEdgeHalfSpaces n := by
  apply Set.Subset.antisymm
  · intro x hx j
    apply convexHull_min (t := {y | directEdgeFunctional n j y ≤ (sequence (n + 1)).core ^ 2})
      _ (convex_halfSpace_le (directEdgeFunctional n j).isLinear _) hx
    rintro _ ⟨k, rfl⟩
    change directEdgeFunctional n j ((directVertex n k).core, (directVertex n k).beam) ≤ _
    rw [edge_apply]
    exact directVertex_mem_edge_halfspace n j k
  · intro x hx
    have hcover : x ∈ ⋃ j, DyadicCone n j := by rw [dyadicCones_cover_plane]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hcover
    obtain ⟨a, b, ha, hb, he⟩ := hj
    let p := orbitPair n j
    let q := orbitPair n (directVertexNext n j)
    let f := directEdgeFunctional n j
    let c := (sequence (n + 1)).core ^ 2
    have hc : 0 < c := pow_pos (core_succ_pos n) _
    have hfp : f p = c := (edge_apply n j _).trans (refinement_midpoint_dot n j).1
    have hfq : f q = c := (edge_apply n j _).trans (refinement_midpoint_dot n j).2.1
    have hfx : f x ≤ c := hx j
    change x = a • p + b • q at he
    rw [he, map_add, map_smul, map_smul, hfp, hfq, smul_eq_mul, smul_eq_mul] at hfx
    have hab : a + b ≤ 1 := (mul_le_mul_iff_right₀ hc).mp (by linarith)
    have hconv : Convex ℝ (directPolygonRegion n) := convex_convexHull ℝ _
    have hp : p ∈ directPolygonRegion n := subset_convexHull ℝ _ ⟨j, rfl⟩
    have hq : q ∈ directPolygonRegion n := subset_convexHull ℝ _ ⟨_, rfl⟩
    by_cases hs : 0 < a + b
    · have hy := hconv hp hq (div_nonneg ha hs.le) (div_nonneg hb hs.le)
        (show a / (a + b) + b / (a + b) = 1 by rw [← add_div, div_self hs.ne'])
      have hz := hconv.smul_mem_of_zero_mem (directPolygonRegion_origin_mem n) hy ⟨hs.le, hab⟩
      have hcancel (u : ℝ) : (a + b) * (u / (a + b)) = u := by field_simp [hs.ne']
      rw [smul_add, smul_smul, smul_smul, hcancel, hcancel, ← he] at hz
      exact hz
    · have ha' : a = 0 := by linarith
      have hb' : b = 0 := by linarith
      rw [he, ha', hb', zero_smul, zero_smul, add_zero]
      exact directPolygonRegion_origin_mem n

/-- 旧辺の両端と奇数頂点から成る、直接軌道の増分三角形。 -/
noncomputable def directRefinementCap (n : ℕ) (j : Fin (4 * 2 ^ n)) : Set (ℝ × ℝ) :=
  convexHull ℝ {orbitPair n j, orbitPair (n + 1) (oddIndex n j),
    orbitPair n (directVertexNext n j)}

/-- 座標対を二次元ユークリッド空間へ移す線形同型。座標基底だけから作る。 -/
noncomputable def directPlaneEquiv : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toLinearEquiv.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearEquiv

/-- 二分核の直接軌道のユークリッド頂点。 -/
noncomputable def intrinsicDirectVertex (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    EuclideanSpace ℝ (Fin 2) :=
  directPlaneEquiv (orbitPair n j)

/-- ユークリッド平面で直接軌道の頂点が張る凸包。 -/
noncomputable def intrinsicDirectPolygonRegion (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ (Set.range (intrinsicDirectVertex n))

/-- 座標の線形同型は直接軌道の凸包をユークリッド版の凸包に移す。 -/
theorem directPlaneEquiv_image_region (n : ℕ) :
    directPlaneEquiv '' directPolygonRegion n = intrinsicDirectPolygonRegion n := by
  change directPlaneEquiv.toLinearMap '' convexHull ℝ (Set.range (orbitPair n)) = _
  rw [LinearMap.image_convexHull]
  apply congrArg (convexHull ℝ)
  ext x
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨orbitPair n j, ⟨j, rfl⟩, rfl⟩

/-- ユークリッド版の凸包は、全辺の内側半平面の共通部分を座標変換した集合に等しい。 -/
theorem intrinsicDirectPolygonRegion_eq_edgeHalfSpaces (n : ℕ) :
    intrinsicDirectPolygonRegion n = directPlaneEquiv '' directEdgeHalfSpaces n := by
  rw [← directPolygonRegion_eq_edgeHalfSpaces, directPlaneEquiv_image_region]

/-- 増分三角形の二辺が張る有向平行四辺形の面積。
新しい二つの隣接外積の和から旧辺の外積を引く。 -/
theorem directRefinementCap_det (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    let p := orbitPair n j
    let w := orbitPair (n + 1) (oddIndex n j)
    let q := orbitPair n (directVertexNext n j)
    (w.1 - p.1) * (q.2 - p.2) - (w.2 - p.2) * (q.1 - p.1) =
      2 * (sequence (n + 1)).beam - (sequence n).beam := by
  dsimp only
  have h₀ := refinement_old_cross n j
  have h₁ := refinement_old_cross (n + 1) (evenIndex n j)
  have h₂ := refinement_old_cross (n + 1) (oddIndex n j)
  rw [directVertexNext_even, directVertex_even] at h₁
  rw [directVertexNext_odd, directVertex_even] at h₂
  unfold orbitPair refinementCross at *
  linarith only [h₀, h₁, h₂]

end DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel
