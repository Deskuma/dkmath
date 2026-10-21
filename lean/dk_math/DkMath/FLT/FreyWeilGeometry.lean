/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Frey
import DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation

#print "file: DkMath.FLT.FreyWeilGeometry"

/-!
# 同じFrey Sourceの曲線上の関数体と平行移動

有理曲線を代数閉包へ基底変換し、実際の座標環のDedekind性を供給する。
同じ曲線の点を用いて、その関数体の自己同型と一般点への作用を構成する。
ねじれ点の基底から人工的な交代形式を選ぶのではなく、曲線の群法を関数へ運んでいる。
Weil対の有理関数・付値計算・ガロア同変性・非退化性は次の課題として残る。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory
open EllipticFunctionField
noncomputable section

local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
variable {p : ℕ} (S : Source p)

/-- 同じ有理曲線を代数閉包へ移しても楕円曲線である。 -/
theorem geometricCurve_isElliptic : (S.rationalCurve⁄(AlgebraicClosure ℚ)).IsElliptic := by
  have := S.rationalCurve_isElliptic
  change (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
  infer_instance

/-- 実際の曲線の幾何学的座標環はDedekind整域である。 -/
theorem geometricCoordinateRing_isDedekindDomain :
    IsDedekindDomain (S.rationalCurve⁄(AlgebraicClosure ℚ)).CoordinateRing := by
  have := S.geometricCurve_isElliptic
  exact EllipticCoordinateRing.isDedekindDomain

/-- 同じ曲線の点による、実際の関数体の平行移動自己同型。 -/
noncomputable def functionFieldTranslation (P : (S.rationalCurve⁄(AlgebraicClosure ℚ)).Point) :
    (S.rationalCurve⁄(AlgebraicClosure ℚ)).FunctionField ≃ₐ[AlgebraicClosure ℚ]
      (S.rationalCurve⁄(AlgebraicClosure ℚ)).FunctionField := by
  classical
  have := S.rationalCurve_isElliptic
  exact transEquiv S.rationalCurve (AlgebraicClosure ℚ) P

/-- 平行移動の合成は、同じ曲線の点群の和に従う。 -/
theorem functionFieldTranslation_add (P Q : (S.rationalCurve⁄(AlgebraicClosure ℚ)).Point) :
    S.functionFieldTranslation (P + Q) =
      (S.functionFieldTranslation Q).trans (S.functionFieldTranslation P) := by
  classical
  have := S.rationalCurve_isElliptic
  exact transEquiv_add _ _ P Q

/-- 零点による移動は恒等同型である。 -/
theorem functionFieldTranslation_zero : S.functionFieldTranslation 0 = AlgEquiv.refl := by
  classical
  have := S.rationalCurve_isElliptic
  exact transEquiv_zero _ _

/-- 異なる点は異なる関数体自己同型を与える。 -/
theorem functionFieldTranslation_injective : Function.Injective S.functionFieldTranslation := by
  classical
  have := S.rationalCurve_isElliptic
  exact transEquiv_injective _ _

end

end DkMath.FLT.Frey.Source
