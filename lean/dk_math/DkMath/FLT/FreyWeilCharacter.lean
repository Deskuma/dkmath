/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilTransport
import DkMath.Lib.NumberTheory.EllipticWeilCharacter

#print "file: DkMath.FLT.FreyWeilCharacter"

/-!
# 同じFrey Sourceの移動固有値とμₙ指標

既存の有理曲線とその関数体から、同じWeil関数の比例定数を取り出す。
Sourceの指数pと倍写像の指数nを区別し、n-torsionの実際の点を引数に取る。
右側変数の加法性・交代性・非退化性を追加の仮定として埋め込まない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
variable {p : ℕ} (S : Source p)

/-- 同じSourceの曲線から構成する非零比例定数。楕円曲線性は実証明から供給する。 -/
noncomputable def curve_weilTranslationUnit (n : ℕ) (hn : n ≠ 0)
    (T Q : Torsion S.rationalCurve n) : (AlgebraicClosure ℚ)ˣ := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit S.rationalCurve n hn T Q

open Classical in
/-- Source入口の比例定数は、既存の同じ候補関数の移動の固有値である。 -/
theorem curve_weilTranslationUnit_spec (n : ℕ) (hn : n ≠ 0) (T Q : Torsion S.rationalCurve n) :
    letI := S.rationalCurve_isElliptic
    transEquiv S.rationalCurve (AlgebraicClosure ℚ) Q.val
      (S.curve_weilFunction n hn T.val T.property) =
      algebraMap (AlgebraicClosure ℚ) (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
        (S.curve_weilTranslationUnit n hn T Q : AlgebraicClosure ℚ) * S.curve_weilFunction n hn T.val T.property := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit_spec S.rationalCurve n hn T Q

/-- 同じSourceの比例定数はn乗根に着地する。 -/
theorem curve_weilTranslationUnit_pow (n : ℕ) (hn : n ≠ 0) (T Q : Torsion S.rationalCurve n) :
    S.curve_weilTranslationUnit n hn T Q ^ n = 1 := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit_pow S.rationalCurve n hn T Q

/-- 固定した実際の目標Tから、μₙに値を持つ片側の加法的指標を構成する。 -/
noncomputable def curve_weilTranslationCharacter (n : ℕ) (hn : n ≠ 0) (T : Torsion S.rationalCurve n) :
    AddChar (Torsion S.rationalCurve n) (rootsOfUnity n (AlgebraicClosure ℚ)) := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationCharacter S.rationalCurve n hn T

/-- Sourceの指標の値は、同じ曲線の同じ移動固有値である。 -/
theorem curve_weilTranslationCharacter_val (n : ℕ) (hn : n ≠ 0) (T Q : Torsion S.rationalCurve n) :
    (S.curve_weilTranslationCharacter n hn T Q).val = S.curve_weilTranslationUnit n hn T Q := rfl

end DkMath.FLT.Frey.Source
