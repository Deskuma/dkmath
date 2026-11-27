/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DirectPolygon
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonMeasure

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicDirectOrbitBridge"

/-!
# 直接生成された軌道と標準角度による軌道の比較

`HalfKernelOrder` は二分核から直接頂点を構成し、その個数を π-free に示す。
ここでは既存の標準角度を使う軌道との一致を証明する。この比較層の依存には
`IntrinsicRegularPolygon` と標準三角関数の bridge が含まれる。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D

/-- 二分核からの直接軌道は既存の等角有限軌道と点ごとに一致する。 -/
theorem directVertex_eq_regularVertex (n : ℕ) (j : Fin (dyadicSides n)) :
    QuadrantUnitKernel.directVertex n j = regularVertex (dyadicSides n) j := by
  unfold QuadrantUnitKernel.directVertex regularVertex kernelOrbitVertex
  rw [regularKernel_dyadic]

open QuadrantUnitKernel

/-- 直接軌道から構成したユークリッド頂点は既存の正多角形の頂点に一致する。 -/
theorem intrinsicDirectVertex_eq_regular (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicDirectVertex n j = (intrinsicRegularPolygon n).vertices j := by
  change pairToEuclideanPlane (directVertex n j).toProd =
    pairToEuclideanPlane (regularVertex (dyadicSides n) j).toProd
  exact congrArg (fun v => pairToEuclideanPlane v.toProd) (directVertex_eq_regularVertex n j)

/-- 対応する頂点が等しいので、直接軌道と既存の正多角形は同じ凸包を張る。 -/
theorem intrinsicDirectPolygonRegion_eq_region (n : ℕ) :
    intrinsicDirectPolygonRegion n = intrinsicPolygonRegion n := by
  apply congrArg (convexHull ℝ)
  apply congrArg Set.range
  exact funext (intrinsicDirectVertex_eq_regular n)

end DkMath.CosmicFormula.Rotation.CF2D
