/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonRefinement
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonCircumscribed
import Mathlib.LinearAlgebra.Dual.Lemmas

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonSupport"

/-! # 標準角度との比較による辺の支持性 -/

namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel
open scoped InnerProductSpace

private theorem vertex_coordinates (n : ℕ) (j : Fin (dyadicSides n)) :
    (intrinsicRegularPolygon n).vertices j 0 = Real.cos (j.val * dyadicAngle n) ∧
    (intrinsicRegularPolygon n).vertices j 1 = Real.sin (j.val * dyadicAngle n) := by
  have ha : normalizedPhaseAngle (j.val • regularPhaseStep (dyadicSides n)) =
      j.val * dyadicAngle n := by
    rw [← regularStepAngle_dyadic]
    simp [normalizedPhaseAngle, nsmul_eq_mul, mul_assoc, mul_left_comm]
  have hv : regularVertex (dyadicSides n) j =
      (realTrigKernelFamily.kernel (normalizedPhaseAngle (j.val • regularPhaseStep (dyadicSides n)))).val := by
    unfold regularVertex kernelOrbitVertex
    rw [UnitKernel.act_vecOne, regularKernel, ← normalizedRealKernelFamily.kernel_nsmul]
    rfl
  simp [intrinsicRegularPolygon, euclideanRegularVertex, hv, show normalizedPhaseAngle (↑j.val * regularPhaseStep (dyadicSides n)) = _ by simpa only [nsmul_eq_mul] using ha, pairToEuclideanPlane,
    Vec.toProd, realTrigKernelFamily]

private theorem dyadicAngle_mul_sides (n : ℕ) :
    (dyadicSides n : ℝ) * dyadicAngle (n + 1) = Real.pi := by
  simp [dyadicSides, dyadicAngle, pow_succ]
  field_simp
  ring

/-- 各辺の中点を法線とする内側半平面に、旧多角形のすべての頂点が入る。
角度の差は半ステップの奇数倍なので、その円周上の距離は半ステップ以上である。 -/
theorem intrinsicPolygon_vertex_mem_edge_halfspace (n : ℕ) (j k : Fin (dyadicSides n)) :
    ⟪midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)),
      (intrinsicRegularPolygon n).vertices k⟫_ℝ ≤ (sequence (n + 1)).core ^ 2 := by
  let d := dyadicAngle (n + 1)
  let t : ℝ := (2 * (k.val : ℝ) - (2 * (j.val : ℝ) + 1)) * d
  have hd : 0 < d := div_pos Real.pi_pos (by positivity)
  have hN : (dyadicSides n : ℝ) * d = Real.pi := dyadicAngle_mul_sides n
  have hj : (j.val : ℝ) + 1 ≤ dyadicSides n := by exact_mod_cast j.isLt
  have hk : (k.val : ℝ) + 1 ≤ dyadicSides n := by exact_mod_cast k.isLt
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have ht : |t| ≤ 2 * Real.pi - d := by
    apply abs_le.mpr
    dsimp [t]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hj) hd.le,
      mul_nonneg (sub_nonneg.mpr hk) hd.le, mul_nonneg hj0 hd.le, mul_nonneg hk0 hd.le]
  have ht' : d ≤ |t| := by
    rcases le_or_gt k.val j.val with h | h
    · have h' : (k.val : ℝ) ≤ j.val := by exact_mod_cast h
      dsimp [t]
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h') hd.le]
    · have h' : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast h
      dsimp [t]
      rw [abs_of_nonneg (mul_nonneg (by linarith) hd.le)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h') hd.le]
  have hcos : Real.cos t ≤ Real.cos d := by
    rw [← Real.cos_abs t]
    by_cases h : |t| ≤ Real.pi
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hd.le h ht'
    · rw [← Real.cos_two_pi_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hd.le (by linarith) (by linarith)
  have hm := intrinsicRegularPolygon_odd_vertex_scaled n j
  have hmid : midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)) =
      (sequence (n + 1)).core • (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n j) := by
    rw [midpoint_eq_smul_add, ← hm, smul_smul]
    congr 1
    norm_num [invOf_eq_inv]
    ring
  rw [hmid, real_inner_smul_left]
  have hc : (sequence (n + 1)).core = Real.cos d := (sequence_trig (n + 1)).1
  have hv := vertex_coordinates (n + 1) (oddIndex n j)
  have hu := vertex_coordinates (n + 1) (evenIndex n k)
  rw [← intrinsicRegularPolygon_even_vertex n k]
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, hv.1, hv.2, hu.1, hu.2]
  have he : ((evenIndex n k).val : ℝ) * d - ((oddIndex n j).val : ℝ) * d = t := by
    simp [evenIndex, oddIndex, t]
    ring
  rw [pow_two]
  apply mul_le_mul_of_nonneg_left _ (core_succ_pos n).le
  rw [← hc, ← he] at hcos
  simpa [Real.cos_sub, mul_comm, d] using hcos

private theorem other_odd_mem_halfspace (n : ℕ) (j k : Fin (dyadicSides n)) (hne : j ≠ k) :
    ⟪midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)),
      (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n k)⟫_ℝ ≤ (sequence (n + 1)).core ^ 2 := by
  let d := dyadicAngle (n + 1)
  let t : ℝ := (2 * (k.val : ℝ) - 2 * (j.val : ℝ)) * d
  have hd : 0 < d := div_pos Real.pi_pos (by positivity)
  have hN : (dyadicSides n : ℝ) * d = Real.pi := dyadicAngle_mul_sides n
  have hj : (j.val : ℝ) + 1 ≤ dyadicSides n := by exact_mod_cast j.isLt
  have hk : (k.val : ℝ) + 1 ≤ dyadicSides n := by exact_mod_cast k.isLt
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have ht : |t| ≤ 2 * Real.pi - d := by
    apply abs_le.mpr
    dsimp [t]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hj) hd.le,
      mul_nonneg (sub_nonneg.mpr hk) hd.le, mul_nonneg hj0 hd.le, mul_nonneg hk0 hd.le]
  have ht' : d ≤ |t| := by
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h).symm) with h | h
    · have h' : (k.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
      dsimp [t]
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h') hd.le]
    · have h' : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast h
      dsimp [t]
      rw [abs_of_nonneg (mul_nonneg (by linarith) hd.le)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h') hd.le]
  have hcos : Real.cos t ≤ Real.cos d := by
    rw [← Real.cos_abs t]
    by_cases h : |t| ≤ Real.pi
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hd.le h ht'
    · rw [← Real.cos_two_pi_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hd.le (by linarith) (by linarith)
  have hm := intrinsicRegularPolygon_odd_vertex_scaled n j
  have hmid : midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)) =
      (sequence (n + 1)).core • (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n j) := by
    rw [midpoint_eq_smul_add, ← hm, smul_smul]
    congr 1
    norm_num [invOf_eq_inv]
    ring
  rw [hmid, real_inner_smul_left]
  have hc : (sequence (n + 1)).core = Real.cos d := (sequence_trig (n + 1)).1
  have hv := vertex_coordinates (n + 1) (oddIndex n j)
  have hu := vertex_coordinates (n + 1) (oddIndex n k)
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, hv.1, hv.2, hu.1, hu.2]
  have he : ((oddIndex n k).val : ℝ) * d - ((oddIndex n j).val : ℝ) * d = t := by
    simp [oddIndex, t]
    ring
  rw [pow_two]
  apply mul_le_mul_of_nonneg_left _ (core_succ_pos n).le
  rw [← hc, ← he] at hcos
  simpa [Real.cos_sub, mul_comm, d] using hcos

/-- 辺の内側半平面は凸なので、全頂点の包含は旧凸包の包含に延びる。 -/
theorem intrinsicPolygonRegion_subset_edgeHalfSpaces (n : ℕ) :
    intrinsicPolygonRegion n ⊆ intrinsicEdgeHalfSpaces n := by
  intro x hx j
  let m := midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
    ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))
  let f := (innerSL ℝ m).toLinearMap
  apply convexHull_min (t := {y | f y ≤ (sequence (n + 1)).core ^ 2}) _
    (convex_halfSpace_le f.isLinear _) hx
  rintro _ ⟨k, rfl⟩
  exact intrinsicPolygon_vertex_mem_edge_halfspace n j k

/-- 増分三角形は旧辺の外側半平面に含まれる。 -/
theorem refinementCap_subset_outer_halfspace (n : ℕ) (j : Fin (dyadicSides n)) :
    let p := (intrinsicRegularPolygon n).vertices j
    let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
    refinementCap n j ⊆ {x | (sequence (n + 1)).core ^ 2 ≤ ⟪midpoint ℝ p q, x⟫_ℝ} := by
  dsimp only
  let p := (intrinsicRegularPolygon n).vertices j
  let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
  let w := (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n j)
  let m := midpoint ℝ p q
  let c := (sequence (n + 1)).core
  have hm : m = c • w := by
    dsimp [m, p, q, c, w]
    rw [midpoint_eq_smul_add, ← intrinsicRegularPolygon_odd_vertex_scaled n j, smul_smul]
    congr 1
    norm_num [invOf_eq_inv]
    ring
  have hn (k : Fin (dyadicSides n)) :
      ‖(intrinsicRegularPolygon n).vertices k‖ = 1 :=
    norm_euclideanRegularVertex _ _
  have he : ⟪m, p⟫_ℝ = ⟪m, q⟫_ℝ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, real_inner_smul_left, real_inner_smul_left,
      inner_add_left, inner_add_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have hp : ‖p‖ = 1 := hn _
    have hq : ‖q‖ = 1 := hn _
    rw [hp, hq, real_inner_comm q p, add_comm]
  have hsum : ⟪m, p⟫_ℝ + ⟪m, q⟫_ℝ = 2 * c ^ 2 := by
    rw [← inner_add_right]
    have h : p + q = (2 : ℝ) • m := by
      dsimp [m]
      rw [midpoint_eq_smul_add, smul_smul]
      norm_num [invOf_eq_inv]
    rw [h, real_inner_smul_right, real_inner_self_eq_norm_sq,
      show ‖m‖ = c from intrinsicPolygon_edge_midpoint_norm n j]
  have hw : c ^ 2 ≤ ⟪m, w⟫_ℝ := by
    rw [hm, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have h : ‖w‖ = 1 := norm_euclideanRegularVertex _ _
    rw [h]
    nlinarith [mul_nonneg (core_succ_pos n).le (sub_nonneg.mpr (core_lt_one (n + 1)).le)]
  let f := (innerSL ℝ m).toLinearMap
  apply convexHull_min _ (convex_halfSpace_ge f.isLinear _)
  intro x hx
  change x ∈ ({p, w, q} : Set EuclideanPlane) at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · change c ^ 2 ≤ ⟪m, p⟫_ℝ
    linarith
  · exact hw
  · change c ^ 2 ≤ ⟪m, q⟫_ℝ
    linarith


/-- 旧領域と増分三角形の共通部分は旧辺の支持直線に含まれる。 -/
theorem refinementCap_inter_old_subset_edge_line (n : ℕ) (j : Fin (dyadicSides n)) :
    let p := (intrinsicRegularPolygon n).vertices j
    let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
    intrinsicPolygonRegion n ∩ refinementCap n j ⊆
      {x | ⟪midpoint ℝ p q, x⟫_ℝ = (sequence (n + 1)).core ^ 2} := by
  dsimp only
  intro x hx
  exact le_antisymm (intrinsicPolygonRegion_subset_edgeHalfSpaces n hx.1 j)
    (refinementCap_subset_outer_halfspace n j hx.2)

private theorem edge_line_null (n : ℕ) (j : Fin (dyadicSides n)) :
    let p := (intrinsicRegularPolygon n).vertices j
    let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
    MeasureTheory.volume {x | ⟪midpoint ℝ p q, x⟫_ℝ = (sequence (n + 1)).core ^ 2} = 0 := by
  dsimp only
  let p := (intrinsicRegularPolygon n).vertices j
  let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
  let m := midpoint ℝ p q
  let f := (innerSL ℝ m).toLinearMap
  let A : AffineSubspace ℝ EuclideanPlane := AffineSubspace.mk' p f.ker
  have hp : f p = (sequence (n + 1)).core ^ 2 :=
    refinementCap_inter_old_subset_edge_line n j
      ⟨subset_convexHull ℝ _ ⟨j, rfl⟩, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
  have hA (x : EuclideanPlane) : x ∈ A ↔ f x = f p := by
    simp [A, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, sub_eq_zero]
  have hproper : A ≠ ⊤ := by
    intro h
    have hz : (0 : EuclideanPlane) ∈ A := h ▸ AffineSubspace.mem_top ℝ EuclideanPlane 0
    have he := (hA 0).mp hz
    rw [map_zero, hp] at he
    exact (ne_of_gt (pow_pos (core_succ_pos n) 2)) he.symm
  apply MeasureTheory.measure_mono_null _ (MeasureTheory.Measure.addHaar_affineSubspace _ A hproper)
  intro x hx
  exact (hA x).mpr (hx.trans hp.symm)

/-- 支持直線は平面の真のアフィン部分空間なので、旧領域と増分三角形の交わりは測度零。 -/
theorem refinementCap_aedisjoint_old_region (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (intrinsicPolygonRegion n) (refinementCap n j) := by
  exact MeasureTheory.measure_mono_null (refinementCap_inter_old_subset_edge_line n j)
    (edge_line_null n j)

/-- 旧領域と全増分三角形の和集合は、測度の意味で交わらない。 -/
theorem refinementCaps_aedisjoint_old_region (n : ℕ) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (intrinsicPolygonRegion n) (⋃ j, refinementCap n j) :=
  MeasureTheory.AEDisjoint.iUnion_right_iff.mpr (refinementCap_aedisjoint_old_region n)

/-- 異なる増分三角形は、一方の旧辺の支持直線を挟むため、交わりの測度は零。 -/
theorem refinementCaps_pairwise_aedisjoint (n : ℕ) :
    Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) (refinementCap n)) := by
  intro j k hjk
  let m := midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
    ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))
  let f := (innerSL ℝ m).toLinearMap
  let c := (sequence (n + 1)).core
  have hk : refinementCap n k ⊆ {x | f x ≤ c ^ 2} := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear _)
    intro x hx
    change x ∈ ({(intrinsicRegularPolygon n).vertices k,
      (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n k),
      (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) k)} : Set EuclideanPlane) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact intrinsicPolygon_vertex_mem_edge_halfspace n j k
    · exact other_odd_mem_halfspace n j k hjk
    · exact intrinsicPolygon_vertex_mem_edge_halfspace n j _
  change MeasureTheory.volume (refinementCap n j ∩ refinementCap n k) = 0
  apply MeasureTheory.measure_mono_null _ (edge_line_null n j)
  intro x hx
  exact le_antisymm (hk hx.2) (refinementCap_subset_outer_halfspace n j hx.1)

private theorem chord_of_level {p q x : EuclideanPlane} {f : EuclideanPlane →ₗ[ℝ] ℝ}
    (hf : f ≠ 0) (hpq : p ≠ q) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hx : ‖x‖ ≤ 1) (heq : f q = f p) (hex : f x = f p) :
    x ∈ segment ℝ p q := by
  let v := q - p
  have hv : v ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hspan : ℝ ∙ v = f.ker := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      simp [v, heq]
    · rw [finrank_span_singleton hv]
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
      rw [finrank_euclideanSpace_fin] at h
      omega
  have hmem : x - p ∈ ℝ ∙ v := by rw [hspan]; simp [hex]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have hxp : x = p + t • v := by rw [ht, add_sub_cancel]
  have hqp : q = p + v := by dsimp [v]; abel
  have hq' := norm_add_sq_real p v
  rw [← hqp, hp, hq] at hq'
  have hx' := norm_add_sq_real p (t • v)
  rw [← hxp, hp, real_inner_smul_right, norm_smul, Real.norm_eq_abs] at hx'
  have hv' : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) _
  have hprod : t * (t - 1) * ‖v‖ ^ 2 ≤ 0 := by
    have hh := congrArg (fun r : ℝ => t * r) hq'
    rw [mul_pow, sq_abs] at hx'
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ 1 + ‖x‖ by positivity)]
  have htt : t * (t - 1) ≤ 0 := nonpos_of_mul_nonpos_left hprod hv'
  rw [segment_eq_image_lineMap]
  refine ⟨t, ⟨?_, ?_⟩, ?_⟩
  · by_contra! h
    exact (not_lt_of_ge htt) (mul_pos_of_neg_of_neg h (by linarith))
  · by_contra! h
    exact (not_lt_of_ge htt) (mul_pos (by linarith) (by linarith))
  · rw [hxp, AffineMap.lineMap_apply_module]
    dsimp [v]
    module

private theorem convex_union_across_level {S T : Set EuclideanPlane}
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (f : EuclideanPlane →ₗ[ℝ] ℝ) (c : ℝ)
    (hs : ∀ x ∈ S, f x ≤ c) (ht : ∀ x ∈ T, c ≤ f x)
    (hc : ∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ segment ℝ x y, f z = c → z ∈ S ∩ T) :
    Convex ℝ (S ∪ T) := by
  have cross : ∀ x ∈ S, ∀ y ∈ T, segment ℝ x y ⊆ S ∪ T := by
    intro x hx y hy
    by_cases h : f x = f y
    · have hy' := (hc x hx y hy y (right_mem_segment ℝ x y) (by linarith [hs x hx, ht y hy])).1
      exact (hS.segment_subset hx hy').trans Set.subset_union_left
    have hp : 0 < f y - f x := sub_pos.mpr (lt_of_le_of_ne ((hs x hx).trans (ht y hy)) h)
    let t := (c - f x) / (f y - f x)
    let z := AffineMap.lineMap x y t
    have hti : t ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (sub_nonneg.mpr (hs x hx)) hp.le,
        (div_le_one hp).mpr (by linarith [ht y hy])⟩
    have hz := lineMap_mem_segment ℝ x y hti
    have hfz : f z = c := by
      dsimp [z]
      rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
      have hmul : t * (f y - f x) = c - f x := div_mul_cancel₀ _ hp.ne'
      simp only [smul_eq_mul]
      nlinarith
    have hzST := hc x hx y hy z hz hfz
    intro w hw
    rw [← insert_endpoints_openSegment] at hw
    simp only [Set.mem_insert_iff] at hw
    rcases hw with rfl | rfl | hw
    · exact Or.inl hx
    · exact Or.inr hy
    have hsplit := openSegment_subset_union x y (z := z) ⟨t, rfl⟩ hw
    simp only [Set.mem_insert_iff, Set.mem_union] at hsplit
    rcases hsplit with rfl | hleft | hright
    · exact Or.inl hzST.1
    · exact Or.inl (hS.segment_subset hx hzST.1 (openSegment_subset_segment _ _ _ hleft))
    · exact Or.inr (hT.segment_subset hzST.2 hy (openSegment_subset_segment _ _ _ hright))
  apply convex_iff_segment_subset.mpr
  intro x hx y hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hS.segment_subset hx hy).trans Set.subset_union_left
  · exact cross x hx y hy
  · rw [segment_symm]
    exact cross y hy x hx
  · exact (hT.segment_subset hx hy).trans Set.subset_union_right

/-- 旧領域に任意の有限個の増分三角形を貼り合わせても凸である。
貼り合わせの支持直線を横切る点は単位円盤内にあり、その直線上の弦は旧辺そのものである。 -/
private theorem convex_partial_caps (n : ℕ) (s : Finset (Fin (dyadicSides n))) :
    Convex ℝ (intrinsicPolygonRegion n ∪ (⋃ j ∈ s, refinementCap n j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty]
    exact convex_convexHull ℝ _
  | @insert j s hj ih =>
    let S := intrinsicPolygonRegion n ∪ (⋃ k ∈ s, refinementCap n k)
    let p := (intrinsicRegularPolygon n).vertices j
    let q := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)
    let m := midpoint ℝ p q
    let f := (innerSL ℝ m).toLinearMap
    let c := (sequence (n + 1)).core ^ 2
    have hp : p ∈ intrinsicPolygonRegion n := subset_convexHull ℝ _ ⟨j, rfl⟩
    have hq : q ∈ intrinsicPolygonRegion n := subset_convexHull ℝ _ ⟨_, rfl⟩
    have hpT : p ∈ refinementCap n j := subset_convexHull ℝ _ (by simp [p])
    have hqT : q ∈ refinementCap n j := subset_convexHull ℝ _ (by simp [q])
    have hfp : f p = c := refinementCap_inter_old_subset_edge_line n j ⟨hp, hpT⟩
    have hfq : f q = c := refinementCap_inter_old_subset_edge_line n j ⟨hq, hqT⟩
    have hf : f ≠ 0 := by
      intro h
      rw [h] at hfp
      exact (ne_of_gt (pow_pos (core_succ_pos n) 2)) hfp.symm
    have hpq : p ≠ q := by
      intro h
      have he := euclideanRegularVertex_injective (dyadicSides_pos n) h
      have hv := congrArg Fin.val he
      change j.val = (j.val + 1) % dyadicSides n at hv
      have hN : 1 < dyadicSides n := by
        unfold dyadicSides
        have := Nat.two_pow_pos n
        omega
      have hlt := j.isLt
      by_cases hh : j.val + 1 < dyadicSides n
      · rw [Nat.mod_eq_of_lt hh] at hv
        omega
      · have heq : j.val + 1 = dyadicSides n := by omega
        rw [heq, Nat.mod_self] at hv
        omega
    have hs : S ⊆ intrinsicPolygonRegion (n + 1) := by
      intro x hx
      apply intrinsicPolygonRefinement_union_subset n
      rcases hx with hx | hx
      · exact Or.inl hx
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hk
        exact Or.inr (Set.mem_iUnion.mpr ⟨k, hx⟩)
    have hT : Convex ℝ (refinementCap n j) := convex_convexHull ℝ _
    have hconv : Convex ℝ (S ∪ refinementCap n j) := by
      apply convex_union_across_level ih hT f c
      · intro x hx
        rcases hx with hx | hx
        · exact intrinsicPolygonRegion_subset_edgeHalfSpaces n hx j
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
          obtain ⟨hks, hx⟩ := Set.mem_iUnion.mp hk
          have hne : j ≠ k := fun he => hj (he ▸ hks)
          apply convexHull_min (t := {x | f x ≤ c}) _ (convex_halfSpace_le f.isLinear _) hx
          intro y hy
          change y ∈ ({(intrinsicRegularPolygon n).vertices k,
            (intrinsicRegularPolygon (n + 1)).vertices (oddIndex n k),
            (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) k)} : Set EuclideanPlane) at hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact intrinsicPolygon_vertex_mem_edge_halfspace n j k
          · exact other_odd_mem_halfspace n j k hne
          · exact intrinsicPolygon_vertex_mem_edge_halfspace n j _
      · exact fun _ hx => refinementCap_subset_outer_halfspace n j hx
      · intro x hx y hy z hz hzf
        have hzN := (convex_convexHull ℝ _).segment_subset (hs hx)
          (intrinsicPolygonRefinement_cap_subset n j hy) hz
        have hnorm : ‖z‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using intrinsicPolygonRegion_subset_closedBall (n + 1) hzN
        have hzseg := chord_of_level hf hpq (norm_euclideanRegularVertex _ _)
          (norm_euclideanRegularVertex _ _) hnorm (hfq.trans hfp.symm) (hzf.trans hfp.symm)
        exact ⟨Or.inl ((convex_convexHull ℝ _).segment_subset hp hq hzseg),
          hT.segment_subset hpT hqT hzseg⟩
    simpa [S, Finset.set_biUnion_insert, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hconv

/-- 次段階の凸包は旧領域と全増分三角形で覆われる。 -/
theorem intrinsicPolygon_refinement_caps (n : ℕ) :
    intrinsicPolygonRegion (n + 1) = intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j) := by
  apply intrinsicPolygon_refinement_caps_of_convex
  simpa using convex_partial_caps n Finset.univ

end DkMath.CosmicFormula.Rotation.CF2D
