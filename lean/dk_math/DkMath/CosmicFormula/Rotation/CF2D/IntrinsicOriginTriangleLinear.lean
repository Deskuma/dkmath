/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonCircumscribed

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicOriginTriangleLinear"

/-!
# 原点三角形と標準三角形の線形像

標準三角形を基底ベクトルと原点の凸包で表し、二つの隣接頂点を列とする
線形写像で移すと原点ファンの三角形が得られる。行列式は `s_n > 0` である。
線形像の測度は行列式の絶対値倍であることも示す。標準三角形の測度が
`1/2` であることは別途必要である。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel
/-- 座標平面の原点と二つの標準基底からなる三角形。 -/
noncomputable def standardTriangle : Set (Fin 2 → ℝ) :=
  convexHull ℝ {0, Pi.single 0 1, Pi.single 1 1}
/-- 標準基底を二つの隣接頂点に送る線形写像。 -/
noncomputable def originTriangleLinearMap (n : ℕ) (j : Fin (dyadicSides n)) :
    (Fin 2 → ℝ) →ₗ[ℝ] EuclideanPlane :=
  (LinearMap.proj 0).smulRight ((intrinsicRegularPolygon n).vertices j) +
  (LinearMap.proj 1).smulRight ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))
/-- 原点三角形は標準三角形の線形像である。 -/
theorem originTriangleLinearMap_image (n : ℕ) (j : Fin (dyadicSides n)) :
    originTriangleLinearMap n j '' standardTriangle = intrinsicOriginTriangle n j := by
  unfold standardTriangle intrinsicOriginTriangle
  rw [LinearMap.image_convexHull]
  congr 1
  simp [originTriangleLinearMap]
/-- 隣接頂点を列として並べた２次正方行列。 -/
noncomputable def originTriangleMatrix (n : ℕ) (j : Fin (dyadicSides n)) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ (intrinsicRegularPolygon n).vertices j 0,
      (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j) 0;
      (intrinsicRegularPolygon n).vertices j 1,
      (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j) 1 ]

/-- この行列の行列式は回転核の beam 座標である。 -/
theorem originTriangleMatrix_det (n : ℕ) (j : Fin (dyadicSides n)) :
    (originTriangleMatrix n j).det = (QuadrantUnitKernel.sequence n).beam := by
  simpa [originTriangleMatrix, Matrix.det_fin_two, vertexCross, mul_comm] using intrinsicPolygon_vertexCross n j

/-- 正の行列式により、標準三角形からの像は退化しない。 -/
theorem originTriangleMatrix_det_pos (n : ℕ) (j : Fin (dyadicSides n)) : 0 < (originTriangleMatrix n j).det := by
  simpa [originTriangleMatrix, Matrix.det_fin_two, vertexCross, mul_comm] using intrinsicOriginTriangle_vertexCross_pos n j

/-- 座標で見た線形写像は、隣接頂点を列とする行列の積に一致する。 -/
theorem originTriangleLinearMap_apply_coordinate (n : ℕ) (j : Fin (dyadicSides n)) (x : Fin 2 → ℝ) (i : Fin 2) :
    originTriangleLinearMap n j x i = (originTriangleMatrix n j).mulVec x i := by
  fin_cases i <;> simp [originTriangleLinearMap, originTriangleMatrix, Matrix.mulVec,
    Matrix.vecHead, Matrix.vecTail, mul_comm]


/--
原点三角形の測度は標準三角形の測度の `s_n` 倍である。

線形写像による測度の変換則と、隣接頂点の行列式 `s_n > 0` を用いる。
標準三角形の測度が `1/2` であることは、この定理の後に別途必要である。
-/
theorem intrinsicOriginTriangle_volume_eq_beam_mul_standard (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((sequence n).beam) * MeasureTheory.volume standardTriangle := by
  let M := originTriangleMatrix n j
  let f := Matrix.toLin' M
  have hstd : IsCompact standardTriangle := (Set.toFinite _).isCompact_convexHull ℝ
  have himg : IsCompact (f '' standardTriangle) := hstd.image (LinearMap.continuous_of_finiteDimensional f)
  have hpre : (WithLp.ofLp : EuclideanPlane → (Fin 2 → ℝ)) ⁻¹' (f '' standardTriangle) = intrinsicOriginTriangle n j := by
    rw [← originTriangleLinearMap_image]
    ext y
    constructor
    · rintro ⟨x, hx, heq⟩
      refine ⟨x, hx, ?_⟩
      ext i
      have hi := congrFun heq i
      simpa [f, Matrix.toLin'_apply, originTriangleLinearMap_apply_coordinate] using hi
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      funext i
      simpa [f, Matrix.toLin'_apply] using (originTriangleLinearMap_apply_coordinate n j x i).symm
  have hvol := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage himg.isClosed.measurableSet.nullMeasurableSet
  rw [hpre] at hvol
  rw [hvol, MeasureTheory.Measure.addHaar_image_linearMap]
  have hdet : LinearMap.det f = M.det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 2))]
    simp [f]
  rw [hdet]
  dsimp [M]
  rw [originTriangleMatrix_det, abs_of_pos (beam_pos n)]


/--
標準三角形の測度が `1/2` であると仮定すると、各原点三角形の測度は `s_n/2` である。
標準三角形の測度公式は明示的な仮定として残る。
-/
theorem intrinsicOriginTriangle_volume_of_standard (n : ℕ) (j : Fin (dyadicSides n))
    (hstandard : MeasureTheory.volume standardTriangle = ENNReal.ofReal (1 / 2)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) = ENNReal.ofReal ((sequence n).beam / 2) := by
  rw [intrinsicOriginTriangle_volume_eq_beam_mul_standard, hstandard,
    ← ENNReal.ofReal_mul (le_of_lt (beam_pos n))]
  congr 1
  ring


/--
標準三角形の面積、原点ファンの被覆、異なる三角形の測度零の重なりを仮定して、
多角形領域の測度を面積候補に同一視する。各仮定は独立した未解決課題である。
-/
theorem intrinsicPolygonRegion_volume_of_standard_origin_fan (n : ℕ)
    (hstandard : MeasureTheory.volume standardTriangle = ENNReal.ofReal (1 / 2))
    (hcover : intrinsicPolygonRegion n = ⋃ j, intrinsicOriginTriangle n j)
    (hdisjoint : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
      (intrinsicOriginTriangle n))) :
    MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_origin_fan n hcover hdisjoint
    (fun j => intrinsicOriginTriangle_volume_of_standard n j hstandard)

end DkMath.CosmicFormula.Rotation.CF2D
