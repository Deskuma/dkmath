/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicOriginTriangleLinear

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicStandardTriangleMeasure"

/-!
# 標準三角形の測度公式と原点ファン

共通の `TriangleMeasure` で得た標準三角形の測度 `1/2` を、
正多角形の原点ファンを構成する線形写像に適用する。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D

/-- 各原点三角形の測度は隣接する回転核の beam の半分である。 -/
theorem intrinsicOriginTriangle_volume (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((QuadrantUnitKernel.sequence n).beam / 2) :=
  intrinsicOriginTriangle_volume_of_standard n j standardTriangle_volume

/-- 原点ファンの被覆と互いの重なりの測度零を仮定した、凸包の面積公式。 -/
theorem intrinsicPolygonRegion_volume_of_origin_fan_geometry (n : ℕ)
    (hcover : intrinsicPolygonRegion n = ⋃ j, intrinsicOriginTriangle n j)
    (hdisjoint : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
      (intrinsicOriginTriangle n))) :
    MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_origin_fan n hcover hdisjoint (intrinsicOriginTriangle_volume n)

end DkMath.CosmicFormula.Rotation.CF2D
