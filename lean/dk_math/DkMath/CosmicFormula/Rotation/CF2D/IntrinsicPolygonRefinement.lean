/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinement
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicDirectOrbitBridge
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonMeasure
import Mathlib.Analysis.Convex.Strict.Extreme

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonRefinement"

/-!
# 二分細分化と凸包の単調性

直接軌道の偶数頂点は元の頂点と一致する。この頂点集合の包含を凸包に移すと
`K_n ⊆ K_(n+1)` が従う。ここでは各辺が二辺に置き換わることや、頂点の
幾何学的な巡回順序、原点ファンの被覆・測度零の交わりは主張しない。
この比較層は既存の標準角度を用いたユークリッド軌道に依存する。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel

/-- ユークリッド軌道でも新しい偶数頂点は元の頂点と一致する。 -/
theorem intrinsicRegularPolygon_even_vertex (n : ℕ) (j : Fin (dyadicSides n)) :
    (intrinsicRegularPolygon (n+1)).vertices (evenIndex n j) =
      (intrinsicRegularPolygon n).vertices j := by
  change pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides (n+1)) (evenIndex n j))) =
    pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides n) j))
  have h1 := directVertex_eq_regularVertex (n+1) (evenIndex n j)
  have h0 := directVertex_eq_regularVertex n j
  have he := directVertex_even n j
  exact congrArg (fun v : Vec ℝ => pairToEuclideanPlane (Vec.toProd v)) (h1.symm.trans (he.trans h0))

/-- 新しい奇数頂点は、古い隣接頂点の中点を単位円まで正規化した点である。
最後の辺でも次頂点は最初の頂点に巡回する。 -/
theorem intrinsicRegularPolygon_odd_vertex_scaled (n : ℕ) (j : Fin (dyadicSides n)) :
    (2 * (sequence (n+1)).core) • (intrinsicRegularPolygon (n+1)).vertices (oddIndex n j) =
      (intrinsicRegularPolygon n).vertices j +
      (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j) := by
  have he := directVertex_odd_scaled n j
  have hodd := directVertex_eq_regularVertex (n+1) (oddIndex n j)
  have hj := directVertex_eq_regularVertex n j
  have hn := directVertex_eq_regularVertex n (directVertexNext n j)
  change directVertex n (directVertexNext n j) =
      regularVertex (dyadicSides n) (regularVertexNext (dyadicSides_pos n) j) at hn
  rw [hodd, hj, hn] at he
  change (2 * (sequence (n+1)).core) •
      pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides (n+1)) (oddIndex n j))) =
      pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides n) j)) +
      pairToEuclideanPlane (Vec.toProd (regularVertex (dyadicSides n) (regularVertexNext (dyadicSides_pos n) j)))
  ext i
  fin_cases i
  · simpa [pairToEuclideanPlane, Vec.toProd] using he.1
  · simpa [pairToEuclideanPlane, Vec.toProd] using he.2

/-- 元の頂点集合は次の段階の頂点集合に含まれる。 -/
theorem intrinsicRegularPolygon_vertices_subset (n : ℕ) :
    Set.range (intrinsicRegularPolygon n).vertices ⊆
      Set.range (intrinsicRegularPolygon (n+1)).vertices := by
  rintro _ ⟨j, rfl⟩
  exact ⟨evenIndex n j, intrinsicRegularPolygon_even_vertex n j⟩

/-- 直接軌道の偶数頂点の保存から、凸包は段階ごとに拡大する。 -/
theorem intrinsicPolygonRegion_succ_subset (n : ℕ) :
    intrinsicPolygonRegion n ⊆ intrinsicPolygonRegion (n+1) := by
  exact convexHull_mono (intrinsicRegularPolygon_vertices_subset n)

/-- 内接多角形の凸包は添字に関して単調非減少である。 -/
theorem intrinsicPolygonRegion_mono : Monotone intrinsicPolygonRegion :=
  monotone_nat_of_le_succ intrinsicPolygonRegion_succ_subset


/-- 新しい奇数頂点は旧凸包には属さない。単位円周上の点は単位円盤の極点であり、旧頂点の凸包の極点なら旧頂点の一つである。しかし偶数添字と奇数添字は一致しない。 -/
theorem refinement_new_vertex_not_mem_old_region (n : ℕ) (j : Fin (dyadicSides n)) :
 (intrinsicRegularPolygon (n+1)).vertices (oddIndex n j) ∉ intrinsicPolygonRegion n := by
  intro hw
  let w := (intrinsicRegularPolygon (n+1)).vertices (oddIndex n j)
  have he : w ∈ (Metric.closedBall (0 : EuclideanPlane) 1).extremePoints ℝ :=
    StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 (by norm_num) (intrinsicRegularPolygon_vertex_mem_sphere (n+1) (oddIndex n j))
  have hex : w ∈ (intrinsicPolygonRegion n).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (intrinsicPolygonRegion_subset_closedBall n) ⟨hw, he⟩
  have hr : w ∈ Set.range (intrinsicRegularPolygon n).vertices :=
    extremePoints_convexHull_subset hex
  obtain ⟨k, hk⟩ := hr
  have hk' : (intrinsicRegularPolygon (n+1)).vertices (evenIndex n k) =
      (intrinsicRegularPolygon (n+1)).vertices (oddIndex n j) := by
    rw [intrinsicRegularPolygon_even_vertex]
    exact hk
  have hi : evenIndex n k = oddIndex n j := by
    apply euclideanRegularVertex_injective (dyadicSides_pos (n+1))
    exact hk'
  have hv := congrArg Fin.val hi
  dsimp [evenIndex, oddIndex] at hv
  omega

/-- 細分化ごとに凸包は真に拡大する。 -/
theorem intrinsicPolygonRegion_succ_ssubset (n : ℕ) : intrinsicPolygonRegion n ⊂ intrinsicPolygonRegion (n+1) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨intrinsicPolygonRegion_succ_subset n, ?_⟩
  intro he
  have h := refinement_new_vertex_not_mem_old_region n ⟨0, dyadicSides_pos n⟩
  apply h
  rw [he]
  exact subset_convexHull ℝ _ ⟨oddIndex n ⟨0, dyadicSides_pos n⟩, rfl⟩


/-- 頂点の二分化による凸包列は真に単調増加する。 -/
theorem intrinsicPolygonRegion_strict_mono : StrictMono intrinsicPolygonRegion :=
  strictMono_nat_of_lt_succ intrinsicPolygonRegion_succ_ssubset

/-- 旧辺の両端と、その辺に対応する新頂点が張る三角形。 -/
noncomputable def refinementCap (n : ℕ) (j : Fin (dyadicSides n)) : Set EuclideanPlane :=
  convexHull ℝ {(intrinsicRegularPolygon n).vertices j,
    (intrinsicRegularPolygon (n+1)).vertices (oddIndex n j),
    (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)}

/-- 増分三角形は次段階の凸包に含まれる。 -/
theorem intrinsicPolygonRefinement_cap_subset (n : ℕ) (j : Fin (dyadicSides n)) :
 refinementCap n j ⊆ intrinsicPolygonRegion (n+1) := by
  unfold refinementCap
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · apply intrinsicPolygonRegion_succ_subset
    exact subset_convexHull ℝ _ ⟨j, rfl⟩
  · exact subset_convexHull ℝ _ ⟨oddIndex n j, rfl⟩
  · apply intrinsicPolygonRegion_succ_subset
    exact subset_convexHull ℝ _ ⟨_, rfl⟩

/-- 旧領域とすべての増分三角形の和集合は次段階の領域に含まれる。 -/
theorem intrinsicPolygonRefinement_union_subset (n : ℕ) : intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j) ⊆ intrinsicPolygonRegion (n+1) := by
  refine Set.union_subset (intrinsicPolygonRegion_succ_subset n) ?_
  exact Set.iUnion_subset (intrinsicPolygonRefinement_cap_subset n)

/-- この和集合が凸であれば次段階の凸包に等しい。凸性そのものは別途必要である。 -/
theorem intrinsicPolygon_refinement_caps_of_convex (n : ℕ)
    (hc : Convex ℝ (intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j))) :
    intrinsicPolygonRegion (n+1) = intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j) := by
  apply Set.Subset.antisymm ?_ (intrinsicPolygonRefinement_union_subset n)
  apply convexHull_min _ hc
  rintro _ ⟨k, rfl⟩
  rcases refinement_index_even_or_odd n k with ⟨j, hj⟩ | ⟨j, hj⟩
  · change Fin (dyadicSides n) at j
    left
    rw [← hj, intrinsicRegularPolygon_even_vertex]
    exact subset_convexHull ℝ _ ⟨j, rfl⟩
  · right
    rw [← hj]
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    apply subset_convexHull ℝ _
    simp



/-- 次段階の凸包は、旧領域と増分三角形の和集合の凸包に等しい。
和集合自体が凸であるかは、この定理では主張しない。 -/
theorem intrinsicPolygon_refinement_caps_convexHull (n : ℕ) : intrinsicPolygonRegion (n+1) =
    convexHull ℝ (intrinsicPolygonRegion n ∪ (⋃ j, refinementCap n j)) := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨k, rfl⟩
    apply subset_convexHull ℝ _
    rcases refinement_index_even_or_odd n k with ⟨j, hj⟩ | ⟨j, hj⟩
    · change Fin (dyadicSides n) at j
      left
      rw [← hj, intrinsicRegularPolygon_even_vertex]
      exact subset_convexHull ℝ _ ⟨j, rfl⟩
    · right
      rw [← hj]
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      apply subset_convexHull ℝ _
      simp
  · exact convexHull_min (intrinsicPolygonRefinement_union_subset n) (convex_convexHull ℝ _)

end DkMath.CosmicFormula.Rotation.CF2D
