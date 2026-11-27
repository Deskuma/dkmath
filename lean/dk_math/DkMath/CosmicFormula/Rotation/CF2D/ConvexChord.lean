/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dual.Lemmas

#print "file: DkMath.CosmicFormula.Rotation.CF2D.ConvexChord"

/-! # 弦と支持直線を使った凸集合の貼り合わせ -/

namespace DkMath.CosmicFormula.Rotation.CF2D

/-- 単位円周上の異なる二点 p, q で同じ値を取る非零線形写像 f を考える。単位円盤内の点 x も同じ値を取るなら、x は線分 pq 上にある。

平面では f の核は一次元で、q − p がこれを張る。よって x = p + t(q − p) と書ける。両端のノルムが 1 であることを使ってノルムの二乗を展開すると、円盤条件は t(t − 1) ≤ 0 を与える。 -/
theorem chord_of_level {p q x : (EuclideanSpace ℝ (Fin 2))} {f : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ}
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

/-- 二つの凸集合が線形汎関数の等位面の両側にあり、両者を結ぶ線分が等位面で両集合に共通する点を通るなら、和集合も凸になる。線分をその点で分け、両側でそれぞれ凸性を適用する。 -/
theorem convex_union_across_level {S T : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    (f : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ) (c : ℝ)
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

end DkMath.CosmicFormula.Rotation.CF2D
