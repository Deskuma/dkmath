/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilGeometry
import DkMath.Lib.NumberTheory.EllipticWeilFunction

#print "file: DkMath.FLT.FreyWeilFunction"

/-!
# 同じFrey Source上のファイバーから有理関数へ

Sourceの指数pと倍写像の指数nを独立に扱う。
同じ有理曲線上で、点のファイバー総和、点イデアルの積の主性、非零分子を供給する。
関数体の商までを構成するが、Weil対や円分行列式の無条件化はまだ結論しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 同じSourceの実際の倍写像のファイバーは、任意の目標点でn²個の点を持つ。 -/
theorem curve_fiber_card (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve) :
    (fiberSet S.rationalCurve n T).ncard = n ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact fiber_card _ n hn T

/-- 同じ曲線上のファイバー総和。目標点のtorsion条件を仮定せずnTと計算する。 -/
theorem curve_fiber_sum (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve) :
    ∃ hfin : (fiberSet S.rationalCurve n T).Finite, ∑ P ∈ hfin.toFinset, P = n • T := by
  have := S.rationalCurve_isElliptic
  exact ⟨fiber_finite _ n hn T, sum_fiber _ n hn T⟩

/-- 同じ曲線のファイバーイデアルが主であるための正確な条件。 -/
theorem curve_fiberIdeal_isPrincipal_iff (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve) :
    letI := S.rationalCurve_isElliptic
    (fiberIdeal S.rationalCurve n hn T).IsPrincipal ↔ n • T = 0 := by
  have := S.rationalCurve_isElliptic
  exact fiberIdeal_isPrincipal_iff _ n hn T

/-- 同じ座標環の非零生成元を持つ実際のファイバーイデアル。 -/
theorem curve_exists_fiber_generator (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) :
    letI := S.rationalCurve_isElliptic
    ∃ f : (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing,
      f ≠ 0 ∧ Ideal.span {f} = fiberIdeal S.rationalCurve n hn T := by
  have := S.rationalCurve_isElliptic
  exact ⟨weilNumerator _ n hn T hT, weilNumerator_ne_zero _ n hn T hT,
    span_weilNumerator _ n hn T hT⟩

/-- 同じ曲線の関数体内に構成した商。Tは実際のn-torsion点でなければならない。 -/
noncomputable def curve_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) : (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField := by
  have := S.rationalCurve_isElliptic
  exact weilFunction _ n hn T hT

/-- 同じSourceの候補関数は非零である。 -/
theorem curve_weilFunction_ne_zero (n : ℕ) (hn : n ≠ 0) (T : Points S.rationalCurve)
    (hT : n • T = 0) : S.curve_weilFunction n hn T hT ≠ 0 := by
  have := S.rationalCurve_isElliptic
  exact weilFunction_ne_zero _ n hn T hT

end DkMath.FLT.Frey.Source
