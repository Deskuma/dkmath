/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicStandardTriangleMeasure

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonAntipodal"

/-!
# 半周対称性と向かい合う原点三角形

各頂点から半周進んだ添字を構成し、対応する頂点が元の頂点の負であることを示す。
この添字は自分自身を逆写像とし、頂点の巡回後継と可換である。
したがって対応する原点三角形は互いに負の像である。
標準三角形の座標の非負性と線形写像の単射性を用いると、向かい合う二つの
三角形の共通部分は原点だけであり、その測度は零である。

これは全ての異なる三角形の測度零の重なりを主張するものではない。
-/
open scoped Pointwise
namespace DkMath.CosmicFormula.Rotation.CF2D
/-- 添字を半周だけ進めた頂点。 -/
noncomputable def intrinsicOppositeIndex (n : ℕ) (j : Fin (dyadicSides n)) : Fin (dyadicSides n) :=
  ⟨(j.val + (intrinsicHalfIndex n).val) % dyadicSides n, Nat.mod_lt _ (dyadicSides_pos n)⟩

/-- 半周先の CF2D 頂点は各座標の符号を反転した点である。 -/
theorem regularVertex_opposite (n : ℕ) (j : Fin (dyadicSides n)) :
    regularVertex (dyadicSides n) (intrinsicOppositeIndex n j) =
      ⟨-(regularVertex (dyadicSides n) j).core, -(regularVertex (dyadicSides n) j).beam⟩ := by
  have hh := regularVertex_intrinsicHalfIndex n
  have hh' : (((regularKernel (dyadicSides n)) ^ (intrinsicHalfIndex n).val : UnitKernel ℝ) : Vec ℝ) = ⟨-1, 0⟩ := by
    simpa [regularVertex, kernelOrbitVertex] using hh
  have hm : (regularKernel (dyadicSides n)) ^ (intrinsicHalfIndex n).val =
      (⟨⟨-1, 0⟩, by norm_num [Vec.q2]⟩ : UnitKernel ℝ) := by
    apply UnitKernel.ext
    exact hh'
  unfold regularVertex kernelOrbitVertex intrinsicOppositeIndex
  simp only [UnitKernel.act_vecOne]
  have hmod : regularKernel (dyadicSides n) ^ ((j.val + (intrinsicHalfIndex n).val) % dyadicSides n) =
      regularKernel (dyadicSides n) ^ (j.val + (intrinsicHalfIndex n).val) := by
    simpa only [orderOf_regularKernel (dyadicSides_pos n)] using
      (pow_mod_orderOf (regularKernel (dyadicSides n)) (j.val + (intrinsicHalfIndex n).val))
  rw [hmod, pow_add, hm, UnitKernel.mul_eq_star, UnitKernel.star_val]
  simp [Vec.star]

/-- ユークリッド平面でも半周先の頂点は元の頂点の負である。 -/
theorem intrinsicRegularPolygon_vertex_opposite (n : ℕ) (j : Fin (dyadicSides n)) :
    (intrinsicRegularPolygon n).vertices (intrinsicOppositeIndex n j) =
      - (intrinsicRegularPolygon n).vertices j := by
  unfold intrinsicRegularPolygon euclideanRegularVertex
  dsimp only
  rw [regularVertex_opposite]
  ext i
  fin_cases i <;> simp [pairToEuclideanPlane, Vec.toProd]

/-- 半周移動を二回行うと元の添字に戻る。 -/
theorem intrinsicOppositeIndex_involution (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicOppositeIndex n (intrinsicOppositeIndex n j) = j := by
  apply Fin.ext
  dsimp [intrinsicOppositeIndex]
  have hh : (intrinsicHalfIndex n).val + (intrinsicHalfIndex n).val = dyadicSides n := by
    simp [intrinsicHalfIndex, dyadicSides]
    omega
  rw [Nat.mod_add_mod, Nat.add_assoc, hh, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]


/-- 半周移動と一辺の巡回移動は可換である。 -/
theorem intrinsicOppositeIndex_next (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicOppositeIndex n (regularVertexNext (dyadicSides_pos n) j) =
      regularVertexNext (dyadicSides_pos n) (intrinsicOppositeIndex n j) := by
  apply Fin.ext
  dsimp [intrinsicOppositeIndex, regularVertexNext]
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega


/-- 半周先の三角形は元の三角形を原点対称に移した集合である。 -/
theorem intrinsicOriginTriangle_opposite (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicOriginTriangle n (intrinsicOppositeIndex n j) = - intrinsicOriginTriangle n j := by
  unfold intrinsicOriginTriangle
  rw [← convexHull_neg]
  rw [← intrinsicOppositeIndex_next, intrinsicRegularPolygon_vertex_opposite, intrinsicRegularPolygon_vertex_opposite]
  simp

/-- 正の行列式により、標準三角形からの線形写像は単射である。 -/
theorem originTriangleLinearMap_injective (n : ℕ) (j : Fin (dyadicSides n)) : Function.Injective (originTriangleLinearMap n j) := by
  have hunit : IsUnit (originTriangleMatrix n j) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact ne_of_gt (originTriangleMatrix_det_pos n j)
  have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hunit
  intro x y h
  apply hinj
  funext i
  rw [← originTriangleLinearMap_apply_coordinate, ← originTriangleLinearMap_apply_coordinate, h]



/-- 向かい合う原点三角形の共通部分は原点のみである。 -/
theorem intrinsicOriginTriangle_inter_opposite (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicOriginTriangle n j ∩ intrinsicOriginTriangle n (intrinsicOppositeIndex n j) = {0} := by
  rw [intrinsicOriginTriangle_opposite]
  apply Set.Subset.antisymm
  · intro x hx
    have hx' := (Set.mem_neg).1 hx.2
    rw [← originTriangleLinearMap_image] at hx' hx
    obtain ⟨a, ha, hax⟩ := hx.1
    obtain ⟨b, hb, hbx⟩ := hx'
    have he : a = -b := by
      apply originTriangleLinearMap_injective n j
      rw [map_neg, hax, hbx, neg_neg]
    have ha0 := (mem_standardTriangle_iff a).1 ha
    have hb0 := (mem_standardTriangle_iff b).1 hb
    have az : a = 0 := by
      funext i
      change a i = 0
      fin_cases i
      · change a 0 = 0
        have h := congrFun he 0
        simp only [Pi.neg_apply] at h
        linarith [ha0.1, hb0.1]
      · change a 1 = 0
        have h := congrFun he 1
        simp only [Pi.neg_apply] at h
        linarith [ha0.2.1, hb0.2.1]
    simp only [Set.mem_singleton_iff]
    rw [az, map_zero] at hax
    exact hax.symm
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    constructor
    · exact subset_convexHull ℝ _ (by simp)
    · apply Set.mem_neg.2
      simp only [neg_zero]
      exact subset_convexHull ℝ _ (by simp)


/-- 向かい合う原点三角形は測度に関して互いに素である。 -/
theorem intrinsicOriginTriangle_aedisjoint_opposite (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (intrinsicOriginTriangle n j)
      (intrinsicOriginTriangle n (intrinsicOppositeIndex n j)) := by
  unfold MeasureTheory.AEDisjoint
  rw [intrinsicOriginTriangle_inter_opposite]
  exact MeasureTheory.measure_singleton 0


/-- 頂点集合は原点対称である。 -/
theorem intrinsicPolygon_vertices_neg (n : ℕ) : -Set.range (intrinsicRegularPolygon n).vertices = Set.range (intrinsicRegularPolygon n).vertices := by
  ext x
  simp only [Set.mem_neg, Set.mem_range]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨intrinsicOppositeIndex n j, ?_⟩
    rw [intrinsicRegularPolygon_vertex_opposite, hj, neg_neg]
  · rintro ⟨j, hj⟩
    refine ⟨intrinsicOppositeIndex n j, ?_⟩
    rw [intrinsicRegularPolygon_vertex_opposite, hj]

/-- 頂点の原点対称性は凸包にも引き継がれる。 -/
theorem intrinsicPolygonRegion_neg (n : ℕ) : -intrinsicPolygonRegion n = intrinsicPolygonRegion n := by
  unfold intrinsicPolygonRegion
  rw [← convexHull_neg]
  congr 1
  ext x
  simp only [Set.mem_neg, Set.mem_range]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨intrinsicOppositeIndex n j, ?_⟩
    rw [intrinsicRegularPolygon_vertex_opposite, hj, neg_neg]
  · rintro ⟨j, hj⟩
    refine ⟨intrinsicOppositeIndex n j, ?_⟩
    rw [intrinsicRegularPolygon_vertex_opposite, hj]

end DkMath.CosmicFormula.Rotation.CF2D
