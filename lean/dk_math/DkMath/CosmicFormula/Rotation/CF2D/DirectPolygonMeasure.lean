/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DirectPolygon
import DkMath.CosmicFormula.Rotation.CF2D.TriangleMeasure

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

end DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel
