/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinement
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicDirectOrbitBridge
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonMeasure

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

end DkMath.CosmicFormula.Rotation.CF2D
