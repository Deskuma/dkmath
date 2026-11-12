/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilValuation
import DkMath.Lib.NumberTheory.EllipticWeilTransport

#print "file: DkMath.FLT.FreyWeilTransport"

/-!
# 同じFrey曲線の無限遠点と平行移動
Sourceの指数pと倍写像の指数nを区別し、既存の曲線・分子・商をそのまま測る。
実際の関数体の自己同型と全点の付値を接続する。比例定数やWeil対データは仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
variable {p : ℕ} (S : Source p)

open Classical in
/-- 同じSourceの分子のノルム次数。零ファイバーに含まれるOだけを除く。 -/
theorem curve_weilNumerator_normDegree (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) :
    letI := S.rationalCurve_isElliptic
    ((Algebra.norm (AlgebraicClosure ℚ)[X] (weilNumerator S.rationalCurve n hn T hT)).natDegree : ℤ) =
      (n : ℤ) ^ 2 - if T = 0 then 1 else 0 := by
  have := S.rationalCurve_isElliptic
  exact normDegree_weilNumerator _ n hn T hT

open Classical in
/-- Oを含む全点の位数。前章の同じ候補関数に適用する。 -/
theorem curve_weilFunction_pointOrder (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) (P : Points S.rationalCurve) :
    letI := S.rationalCurve_isElliptic
    pointOrder S.rationalCurve P (S.curve_weilFunction n hn T hT)
      (S.curve_weilFunction_ne_zero n hn T hT) =
      (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) := by
  have := S.rationalCurve_isElliptic
  exact pointOrder_weilFunction _ n hn T hT P

open Classical in
/-- n-torsionによる移動で、同じ候補関数の全点の位数が保存される。 -/
theorem curve_weilFunction_pointOrder_transEquiv (n : ℕ) (hn : n ≠ 0)
    (T : Points S.rationalCurve) (hT : n • T = 0) (P Q : Points S.rationalCurve) (hQ : n • Q = 0) :
    letI := S.rationalCurve_isElliptic
    pointOrder S.rationalCurve P
      (transEquiv S.rationalCurve (AlgebraicClosure ℚ) Q (S.curve_weilFunction n hn T hT))
      ((transEquiv S.rationalCurve (AlgebraicClosure ℚ) Q).toRingEquiv.map_ne_zero_iff.mpr
        (S.curve_weilFunction_ne_zero n hn T hT)) =
      pointOrder S.rationalCurve P (S.curve_weilFunction n hn T hT)
        (S.curve_weilFunction_ne_zero n hn T hT) := by
  have := S.rationalCurve_isElliptic
  exact pointOrder_transEquiv_weilFunction_of_torsion _ n hn T hT P Q hQ

end DkMath.FLT.Frey.Source
