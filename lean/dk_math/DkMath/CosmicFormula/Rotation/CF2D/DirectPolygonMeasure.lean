/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DirectPolygon
import DkMath.CosmicFormula.Rotation.CF2D.TriangleMeasure
import DkMath.CosmicFormula.Rotation.CF2D.ConvexChord

#print "file: DkMath.CosmicFormula.Rotation.CF2D.DirectPolygonMeasure"

/-! # 直接軌道から作る増分三角形の測度 -/

namespace DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel
open MeasureTheory

/-- 旧辺の両端と奇数頂点のユークリッド座標が張る増分三角形。 -/
noncomputable def intrinsicDirectRefinementCap (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {intrinsicDirectVertex n j, intrinsicDirectVertex (n + 1) (oddIndex n j),
    intrinsicDirectVertex n (directVertexNext n j)}

/-- 増分三角形の面積は、正の行列式の半分である。
二分核の倍角関係から、行列式は `2 (1 - c_(n+1)) s_(n+1)` となる。 -/
theorem intrinsicDirectRefinementCap_volume (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    volume (intrinsicDirectRefinementCap n j) =
      ENNReal.ofReal ((sequence (n + 1)).beam - (sequence n).beam / 2) := by
  unfold intrinsicDirectRefinementCap
  rw [euclideanTriangle_volume_eq_abs_det]
  have h := directRefinementCap_det n j
  change ((intrinsicDirectVertex (n + 1) (oddIndex n j) - intrinsicDirectVertex n j) 0 *
      (intrinsicDirectVertex n (directVertexNext n j) - intrinsicDirectVertex n j) 1 -
      (intrinsicDirectVertex (n + 1) (oddIndex n j) - intrinsicDirectVertex n j) 1 *
      (intrinsicDirectVertex n (directVertexNext n j) - intrinsicDirectVertex n j) 0) = _ at h
  rw [h, abs_of_pos]
  · congr 1
    ring
  · rw [refinement_beam n]
    nlinarith [mul_pos (sub_pos.mpr (core_lt_one (n + 1))) (beam_pos (n + 1))]

/-- 直接増分三角形の個別測度を全辺で足すと、面積候補の一段分の差になる。 -/
theorem intrinsicDirectRefinementCaps_sum_volume (n : ℕ) :
    (∑ j : Fin (4 * 2 ^ n), volume (intrinsicDirectRefinementCap n j)) =
      ENNReal.ofReal (areaApprox (n + 1) - areaApprox n) := by
  simp only [intrinsicDirectRefinementCap_volume, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, areaApprox, pow_succ]
  ring

/-- 増分三角形は次段階の凸包に含まれる。旧端点は偶数添字に、新頂点は奇数添字に現れる。 -/
theorem intrinsicDirectRefinementCap_subset_succ (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    intrinsicDirectRefinementCap n j ⊆ intrinsicDirectPolygonRegion (n + 1) := by
  have he (k : Fin (4 * 2 ^ n)) :
      intrinsicDirectVertex (n + 1) (evenIndex n k) = intrinsicDirectVertex n k := by
    unfold intrinsicDirectVertex orbitPair
    rw [directVertex_even]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  change x ∈ ({intrinsicDirectVertex n j, intrinsicDirectVertex (n + 1) (oddIndex n j),
    intrinsicDirectVertex n (directVertexNext n j)} : Set (EuclideanSpace ℝ (Fin 2))) at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact subset_convexHull ℝ _ ⟨evenIndex n j, he j⟩
  · exact subset_convexHull ℝ _ ⟨oddIndex n j, rfl⟩
  · exact subset_convexHull ℝ _ ⟨evenIndex n (directVertexNext n j), he _⟩

/-- 旧凸包と全増分三角形の和集合は次段階の凸包を生成する。
逆包含に凸包を外すには、和集合自体の凸性を示す必要がある。 -/
theorem intrinsicDirectPolygonRegion_succ_eq_convexHull_caps (n : ℕ) :
    intrinsicDirectPolygonRegion (n + 1) = convexHull ℝ
      (intrinsicDirectPolygonRegion n ∪ ⋃ j, intrinsicDirectRefinementCap n j) := by
  have he (j : Fin (4 * 2 ^ n)) :
      intrinsicDirectVertex (n + 1) (evenIndex n j) = intrinsicDirectVertex n j := by
    unfold intrinsicDirectVertex orbitPair
    rw [directVertex_even]
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨k, rfl⟩
    apply subset_convexHull ℝ _
    rcases refinement_index_even_or_odd n k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ((he j).symm ▸ subset_convexHull ℝ (Set.range (intrinsicDirectVertex n)) ⟨j, rfl⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, subset_convexHull ℝ _ (by simp)⟩)
  · apply convexHull_min _ (convex_convexHull ℝ _)
    apply Set.union_subset
    · apply convexHull_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨evenIndex n j, he j⟩
    · exact Set.iUnion_subset (intrinsicDirectRefinementCap_subset_succ n)

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "K" => intrinsicDirectPolygonRegion
local notation "C" => intrinsicDirectRefinementCap
local notation "V" => intrinsicDirectVertex

private noncomputable def edgeOnPlane (n : ℕ) (j : Fin (4 * 2 ^ n)) : Plane →ₗ[ℝ] ℝ :=
  (directEdgeFunctional n j).comp directPlaneEquiv.symm.toLinearMap

private theorem edgeOnPlane_vertex (n m : ℕ) (j : Fin (4 * 2 ^ n)) (k : Fin (4 * 2 ^ m)) :
    edgeOnPlane n j (V m k) =
      refinementDot (refinementMidpoint (directVertex n j)
        (directVertex n (directVertexNext n j))) (directVertex m k) := by
  simp [edgeOnPlane, intrinsicDirectVertex, directEdgeFunctional, orbitPair, refinementDot,
    smul_eq_mul]

private theorem edge_old_le (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    K n ⊆ {x | edgeOnPlane n j x ≤ (sequence (n + 1)).core ^ 2} := by
  apply convexHull_min _ (convex_halfSpace_le (edgeOnPlane n j).isLinear _)
  rintro _ ⟨k, rfl⟩
  exact (edgeOnPlane_vertex n n j k).trans_le (directVertex_mem_edge_halfspace n j k)

private theorem edge_cap_ge (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    C n j ⊆ {x | (sequence (n + 1)).core ^ 2 ≤ edgeOnPlane n j x} := by
  apply convexHull_min _ (convex_halfSpace_ge (edgeOnPlane n j).isLinear _)
  intro x hx
  change x ∈ ({V n j, V (n + 1) (oddIndex n j), V n (directVertexNext n j)} : Set Plane) at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ((edgeOnPlane_vertex n n j j).trans (refinement_midpoint_dot n j).1).ge
  · change _ ≤ edgeOnPlane n j (V (n + 1) (oddIndex n j))
    rw [edgeOnPlane_vertex, (refinement_midpoint_dot n j).2.2]
    nlinarith [mul_nonneg (core_succ_pos n).le (sub_nonneg.mpr (core_lt_one (n + 1)).le)]
  · exact ((edgeOnPlane_vertex n n j _).trans (refinement_midpoint_dot n j).2.1).ge

private theorem edge_other_cap_le (n : ℕ) (j k : Fin (4 * 2 ^ n)) (h : j ≠ k) :
    C n k ⊆ {x | edgeOnPlane n j x ≤ (sequence (n + 1)).core ^ 2} := by
  apply convexHull_min _ (convex_halfSpace_le (edgeOnPlane n j).isLinear _)
  intro x hx
  change x ∈ ({V n k, V (n + 1) (oddIndex n k), V n (directVertexNext n k)} : Set Plane) at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact (edgeOnPlane_vertex n n j k).trans_le (directVertex_mem_edge_halfspace n j k)
  · exact (edgeOnPlane_vertex n (n + 1) j _).trans_le (other_odd_mem_halfspace_pi_free n j k h)
  · exact (edgeOnPlane_vertex n n j _).trans_le (directVertex_mem_edge_halfspace n j _)

private theorem edge_line_null_direct (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    volume {x | edgeOnPlane n j x = (sequence (n + 1)).core ^ 2} = 0 := by
  let f := edgeOnPlane n j
  let p := V n j
  let A : AffineSubspace ℝ Plane := AffineSubspace.mk' p f.ker
  have hp : f p = (sequence (n + 1)).core ^ 2 :=
    (edgeOnPlane_vertex n n j j).trans (refinement_midpoint_dot n j).1
  have hA (x : Plane) : x ∈ A ↔ f x = f p := by
    simp [A, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, sub_eq_zero]
  have hproper : A ≠ ⊤ := by
    intro h
    have hz : (0 : Plane) ∈ A := h ▸ AffineSubspace.mem_top ℝ Plane 0
    have he := (hA 0).mp hz
    rw [map_zero, hp] at he
    exact (ne_of_gt (pow_pos (core_succ_pos n) 2)) he.symm
  apply measure_mono_null _ (Measure.addHaar_affineSubspace _ A hproper)
  intro x hx
  exact (hA x).mpr (hx.trans hp.symm)

/-- 旧凸包と全増分三角形は支持直線を除いて交わらない。 -/
theorem intrinsicDirectCaps_aedisjoint_old (n : ℕ) :
    AEDisjoint volume (K n) (⋃ j, C n j) := by
  apply AEDisjoint.iUnion_right_iff.mpr
  intro j
  apply measure_mono_null _ (edge_line_null_direct n j)
  intro x hx
  exact le_antisymm (edge_old_le n j hx.1) (edge_cap_ge n j hx.2)

/-- 異なる増分三角形の交わりは一方の旧辺の支持直線に含まれ、測度零である。 -/
theorem intrinsicDirectCaps_pairwise_aedisjoint (n : ℕ) :
    Pairwise (Function.onFun (AEDisjoint volume) (C n)) := by
  intro j k h
  apply measure_mono_null _ (edge_line_null_direct n j)
  intro x hx
  exact le_antisymm (edge_other_cap_le n j k h hx.2) (edge_cap_ge n j hx.1)

private theorem directVertex_norm (n : ℕ) (j : Fin (4 * 2 ^ n)) : ‖V n j‖ = 1 := by
  have h : ‖V n j‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    exact directVertex_q2 n j
  nlinarith [norm_nonneg (V n j)]

private theorem directRegion_subset_ball (n : ℕ) : K n ⊆ Metric.closedBall (0 : Plane) 1 := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨j, rfl⟩
  simp [Metric.mem_closedBall, dist_zero_right, directVertex_norm]

private theorem directRegion_subset_succ (n : ℕ) : K n ⊆ K (n + 1) := by
  apply convexHull_mono
  rintro _ ⟨j, rfl⟩
  refine ⟨evenIndex n j, ?_⟩
  unfold intrinsicDirectVertex orbitPair
  rw [directVertex_even]

private theorem directVertex_pair_injective (n : ℕ) : Function.Injective (V n) := by
  intro i j h
  have e := directPlaneEquiv.injective h
  apply directVertex_injective n
  exact congrArg (fun z : ℝ × ℝ => Vec.mk z.1 z.2) e

/-- 旧領域に任意の有限個の増分三角形を貼り合わせても凸である。
貼り合わせの支持直線を横切る点は単位円盤内にあり、その直線上の弦は旧辺そのものである。 -/
private theorem convex_partial_direct_caps (n : ℕ) (s : Finset (Fin (4 * 2 ^ n))) :
    Convex ℝ (K n ∪ (⋃ j ∈ s, C n j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty]
    exact convex_convexHull ℝ _
  | @insert j s hj ih =>
    let S := K n ∪ (⋃ k ∈ s, C n k)
    let p := V n j
    let q := V n (directVertexNext n j)
    let f := edgeOnPlane n j
    let c := (sequence (n + 1)).core ^ 2
    have hp : p ∈ K n := subset_convexHull ℝ _ ⟨j, rfl⟩
    have hq : q ∈ K n := subset_convexHull ℝ _ ⟨_, rfl⟩
    have hpT : p ∈ C n j := subset_convexHull ℝ _ (by simp [p])
    have hqT : q ∈ C n j := subset_convexHull ℝ _ (by simp [q])
    have hfp : f p = c := (edgeOnPlane_vertex n n j j).trans (refinement_midpoint_dot n j).1
    have hfq : f q = c := (edgeOnPlane_vertex n n j _).trans (refinement_midpoint_dot n j).2.1
    have hf : f ≠ 0 := by
      intro h
      rw [h] at hfp
      exact (ne_of_gt (pow_pos (core_succ_pos n) 2)) hfp.symm
    have hpq : p ≠ q := by
      intro h
      have he := directVertex_pair_injective n h
      have hv := congrArg Fin.val he
      change j.val = (j.val + 1) % (4 * 2 ^ n) at hv
      have hN : 1 < (4 * 2 ^ n) := by
        have := Nat.two_pow_pos n
        omega
      have hlt := j.isLt
      by_cases hh : j.val + 1 < (4 * 2 ^ n)
      · rw [Nat.mod_eq_of_lt hh] at hv
        omega
      · have heq : j.val + 1 = (4 * 2 ^ n) := by omega
        rw [heq, Nat.mod_self] at hv
        omega
    have hs : S ⊆ K (n + 1) := by
      intro x hx
      rcases hx with hx | hx
      · exact directRegion_subset_succ n hx
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hk
        exact intrinsicDirectRefinementCap_subset_succ n k hx
    have hT : Convex ℝ (C n j) := convex_convexHull ℝ _
    have hconv : Convex ℝ (S ∪ C n j) := by
      apply convex_union_across_level ih hT f c
      · intro x hx
        rcases hx with hx | hx
        · exact edge_old_le n j hx
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
          obtain ⟨hks, hx⟩ := Set.mem_iUnion.mp hk
          have hne : j ≠ k := fun he => hj (he ▸ hks)
          exact edge_other_cap_le n j k hne hx
      · exact fun _ hx => edge_cap_ge n j hx
      · intro x hx y hy z hz hzf
        have hzN := (convex_convexHull ℝ _).segment_subset (hs hx)
          (intrinsicDirectRefinementCap_subset_succ n j hy) hz
        have hnorm : ‖z‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using directRegion_subset_ball (n + 1) hzN
        have hzseg := chord_of_level hf hpq (directVertex_norm _ _)
          (directVertex_norm _ _) hnorm (hfq.trans hfp.symm) (hzf.trans hfp.symm)
        exact ⟨Or.inl ((convex_convexHull ℝ _).segment_subset hp hq hzseg),
          hT.segment_subset hpT hqT hzseg⟩
    simpa [S, Finset.set_biUnion_insert, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hconv

/-- 全増分三角形を旧凸包へ貼り合わせると次段階の凸包になる。 -/
theorem intrinsicDirectPolygon_refinement_caps (n : ℕ) :
    K (n + 1) = K n ∪ ⋃ j, C n j := by
  rw [intrinsicDirectPolygonRegion_succ_eq_convexHull_caps]
  exact (show Convex ℝ (K n ∪ ⋃ j, C n j) by
    simpa using convex_partial_direct_caps n Finset.univ).convexHull_eq

/-- 初期正方形は対角線で二つの面積 1 の三角形に分かれる。 -/
theorem intrinsicDirectPolygonRegion_zero_volume : volume (K 0) = ENNReal.ofReal 2 := by
  let p := V 0 0
  let q := V 0 2
  let u := V 0 1
  let v := V 0 3
  let S := convexHull ℝ ({p, v, q} : Set Plane)
  let T := convexHull ℝ ({p, u, q} : Set Plane)
  let f := (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap
  have coords (j : Fin 4) (i : Fin 2) :
      V 0 j i = ![(![1, 0] : Fin 2 → ℝ), ![0, 1], ![-1, 0], ![0, -1]] j i := by
    fin_cases j <;> fin_cases i <;>
      simp [intrinsicDirectVertex, orbitPair_zero, directPlaneEquiv]
  have fp : f p = 0 := coords 0 1
  have fq : f q = 0 := coords 2 1
  have fu : f u = 1 := coords 1 1
  have fv : f v = -1 := coords 3 1
  have hpq : p ≠ q := by
    intro h
    have e := congrArg (fun z : Plane => z 0) h
    change V 0 0 0 = V 0 2 0 at e
    rw [coords, coords] at e
    norm_num at e
  have hf : f ≠ 0 := by
    intro h
    rw [h, LinearMap.zero_apply] at fu
    norm_num at fu
  have hs : S ⊆ {x | f x ≤ 0} := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [fp, fq, fv]
  have ht : T ⊆ {x | 0 ≤ f x} := by
    apply convexHull_min _ (convex_halfSpace_ge f.isLinear _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [fp, fq, fu]
  have hS : S ⊆ K 0 := by
    apply convexHull_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
  have hT : T ⊆ K 0 := by
    apply convexHull_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hconv : Convex ℝ (S ∪ T) := by
    apply convex_union_across_level (convex_convexHull ℝ _) (convex_convexHull ℝ _) f 0 hs ht
    intro x hx y hy z hz hz0
    have hz' := (convex_convexHull ℝ _).segment_subset (hS hx) (hT hy) hz
    have hn : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using directRegion_subset_ball 0 hz'
    have hseg := chord_of_level hf hpq (directVertex_norm 0 0) (directVertex_norm 0 2)
      hn (fq.trans fp.symm) (hz0.trans fp.symm)
    exact ⟨segment_subset_convexHull (by simp) (by simp) hseg,
      segment_subset_convexHull (by simp) (by simp) hseg⟩
  have he : K 0 = S ∪ T := by
    apply Set.Subset.antisymm _ (Set.union_subset hS hT)
    apply convexHull_min _ hconv
    rintro _ ⟨j, rfl⟩
    change Fin 4 at j
    fin_cases j
    · exact Or.inl (subset_convexHull ℝ _ (by change p ∈ _; simp))
    · exact Or.inr (subset_convexHull ℝ _ (by change u ∈ _; simp))
    · exact Or.inl (subset_convexHull ℝ _ (by change q ∈ _; simp))
    · exact Or.inl (subset_convexHull ℝ _ (by change v ∈ _; simp))
  have hd : AEDisjoint volume S T := by
    let A : AffineSubspace ℝ Plane := AffineSubspace.mk' 0 f.ker
    have hA (x : Plane) : x ∈ A ↔ f x = 0 := by
      simp [A, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub]
    have hproper : A ≠ ⊤ := by
      intro h
      have hmem : u ∈ A := h ▸ AffineSubspace.mem_top ℝ Plane u
      have e := (hA u).mp hmem
      rw [fu] at e
      norm_num at e
    apply measure_mono_null _ (Measure.addHaar_affineSubspace _ A hproper)
    intro x hx
    exact (hA x).mpr (le_antisymm (hs hx.1) (ht hx.2))
  have hm : NullMeasurableSet T volume :=
    ((Set.toFinite _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet
  rw [he, measure_union₀ hm hd]
  unfold S T p q u v
  rw [euclideanTriangle_volume_eq_abs_det, euclideanTriangle_volume_eq_abs_det]
  norm_num [PiLp.sub_apply, coords, ENNReal.ofReal_ofNat]

/-- 被覆と零交差から、すべての直接凸包の測度は面積候補に一致する。 -/
theorem intrinsicDirectPolygonRegion_volume_eq_areaApprox (n : ℕ) :
    volume (K n) = ENNReal.ofReal (areaApprox n) := by
  induction n with
  | zero => rw [intrinsicDirectPolygonRegion_zero_volume, areaApprox_zero]
  | succ n ih =>
    have hm : NullMeasurableSet (K n) volume :=
      (Set.finite_range (V n)).isCompact_convexHull ℝ |>.isClosed.measurableSet.nullMeasurableSet
    rw [intrinsicDirectPolygon_refinement_caps, measure_union₀' hm
      (intrinsicDirectCaps_aedisjoint_old n), measure_iUnion₀ (intrinsicDirectCaps_pairwise_aedisjoint n),
      tsum_fintype, intrinsicDirectRefinementCaps_sum_volume, ih]
    · rw [← ENNReal.ofReal_add (areaApprox_nonneg n)
        (sub_nonneg.mpr (areaApprox_monotone (Nat.le_succ n)))]
      congr 1
      ring
    · intro j
      exact ((Set.toFinite _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet

open scoped InnerProductSpace Pointwise Topology
open Filter

/-- 各辺の法線は、対応する奇数頂点を内接円の半径で縮めたものである。 -/
private theorem edgeOnPlane_eq_inner (n : ℕ) (j : Fin (4 * 2 ^ n)) (x : Plane) :
    edgeOnPlane n j x =
      (sequence (n + 1)).core * ⟪V (n + 1) (oddIndex n j), x⟫_ℝ := by
  have h := directVertex_odd_scaled n j
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  change ((directVertex n j).core + (directVertex n (directVertexNext n j)).core) / 2 * x 0 +
    ((directVertex n j).beam + (directVertex n (directVertexNext n j)).beam) / 2 * x 1 =
    (sequence (n + 1)).core *
      (x 0 * (directVertex (n + 1) (oddIndex n j)).core +
       x 1 * (directVertex (n + 1) (oddIndex n j)).beam)
  rw [← h.1, ← h.2]
  ring

/-- 半径が半角核の第一座標である閉円盤は、直接軌道の凸包に入る。 -/
theorem intrinsicDirectInnerBall_subset (n : ℕ) :
    Metric.closedBall (0 : Plane) (sequence (n + 1)).core ⊆ K n := by
  intro x hx
  rw [intrinsicDirectPolygonRegion_eq_edgeHalfSpaces]
  refine ⟨directPlaneEquiv.symm x, ?_, directPlaneEquiv.apply_symm_apply x⟩
  intro j
  change edgeOnPlane n j x ≤ _
  rw [edgeOnPlane_eq_inner]
  have hn : ‖x‖ ≤ (sequence (n + 1)).core := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hi := real_inner_le_norm (V (n + 1) (oddIndex n j)) x
  rw [directVertex_norm, one_mul] at hi
  simpa only [pow_two] using mul_le_mul_of_nonneg_left (hi.trans hn) (core_succ_pos n).le

/-- 単位閉円盤の実数値測度を、直接軌道の内外多角形で挟む。
この証明は直接軌道と標準角度の比較を必要としない。 -/
theorem direct_disk_measureReal_eq_intrinsicPi :
    volume.real (Metric.closedBall (0 : Plane) 1) = intrinsicPi := by
  let disk := Metric.closedBall (0 : Plane) 1
  have hlower (n : ℕ) : areaApprox n ≤ volume.real disk := by
    have h := measureReal_mono (μ := volume) (directRegion_subset_ball n)
      ((isCompact_closedBall (0 : Plane) 1).measure_lt_top.ne)
    rw [measureReal_def, intrinsicDirectPolygonRegion_volume_eq_areaApprox,
      ENNReal.toReal_ofReal (areaApprox_nonneg n)] at h
    exact h
  have hupper (n : ℕ) : volume.real disk ≤ outerApprox n := by
    let c := (sequence (n + 1)).core
    have hc : 0 < c := core_succ_pos n
    have hcover : disk ⊆ c⁻¹ • K n := by
      intro x hx
      have hn : ‖x‖ ≤ 1 := by simpa [disk, Metric.mem_closedBall, dist_zero_right] using hx
      refine ⟨c • x, intrinsicDirectInnerBall_subset n ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hc.le
      · change c⁻¹ • (c • x) = x
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    have hv : volume (c⁻¹ • K n) = ENNReal.ofReal (outerApprox n) := by
      rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg _),
        intrinsicDirectPolygonRegion_volume_eq_areaApprox, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      rw [outerApprox_eq_areaApprox_div_core_sq]
      change c⁻¹ ^ 2 * areaApprox n = areaApprox n / c ^ 2
      ring
    have h := measureReal_mono (μ := volume) hcover (by rw [hv]; exact ENNReal.ofReal_ne_top)
    simp only [measureReal_def] at h
    rw [hv, ENNReal.toReal_ofReal] at h
    · exact h
    · exact div_nonneg (areaApprox_nonneg _) (core_succ_pos n).le
  exact le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds tendsto_outerApprox_intrinsicPi hupper)
    (le_of_tendsto_of_tendsto' tendsto_areaApprox_intrinsicPi tendsto_const_nhds hlower)

end DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel
