/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilFunction
import DkMath.Lib.NumberTheory.EllipticWeilValuation

#print "file: DkMath.FLT.FreyWeilValuation"

/-!
# 同じFrey Sourceの候補関数の零点と極を測る

前章で構成した曲線・分子・商をそのまま用いる。
座標環のDedekind性は証明から供給し、P≠Oの有限点に限って位数を計算する。
Sourceの指数pと倍写像の指数nを区別し、Weil対データを仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

open Classical in
/-- 同じ実際のWeil分子は、nP=Tの有限点でちょうど一重に消える。 -/
theorem curve_weilNumerator_order (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) (P : Points S.rationalCurve) (hP : P ≠ 0) :
    letI := S.rationalCurve_isElliptic
    finitePointOrder S.rationalCurve P hP
      (algebraMap (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
        (weilNumerator S.rationalCurve n hn T hT))
      (algebraMap_weilNumerator_ne_zero _ n hn T hT) = if n • P = T then 1 else 0 := by
  have := S.rationalCurve_isElliptic
  exact order_weilNumerator _ n hn T hT P hP

open Classical in
/-- 前章の同じSourceの商の乗法的付値。新しい候補関数へ置き換えない。 -/
theorem curve_weilFunction_valuation (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) (P : Points S.rationalCurve) (hP : P ≠ 0) :
    letI := S.rationalCurve_isElliptic
    finitePointValuation S.rationalCurve P hP (S.curve_weilFunction n hn T hT) =
      (if n • P = T then exp (-1 : ℤ) else 1) /
      (if n • P = 0 then exp (-1 : ℤ) else 1) := by
  have := S.rationalCurve_isElliptic
  exact valuation_weilFunction _ n hn T hT P hP

open Classical in
/-- 零点は正、極は負とする整数位数。同じSourceの商の位数はファイバー指示関数の差。 -/
theorem curve_weilFunction_order (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) (P : Points S.rationalCurve) (hP : P ≠ 0) :
    letI := S.rationalCurve_isElliptic
    finitePointOrder S.rationalCurve P hP (S.curve_weilFunction n hn T hT)
      (S.curve_weilFunction_ne_zero n hn T hT) =
      (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) := by
  have := S.rationalCurve_isElliptic
  exact order_weilFunction _ n hn T hT P hP

end DkMath.FLT.Frey.Source
