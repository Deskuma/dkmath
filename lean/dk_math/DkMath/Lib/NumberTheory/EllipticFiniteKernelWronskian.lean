/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPair

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskian"

/-!
# Vélu 補正項の形式微分と Wronskian

`xCorrection` は

`t/(X-a) + u/(X-a)^2`

という有理式であり、`zCorrection` はその形式微分に対応する
`-t/(X-a)^2 - 2u/(X-a)^3` である。本ファイルでは分母を払った
多項式分子を導入し、形式微分の Wronskian が `X-a` と z 分子の積に
なることを、有限核や二捩れ点を仮定せずに証明する。

この恒等式は、`veluX_half` と `veluZ_half` の有限和へ進む際の代数的な
接続点である。ここで証明するのは一つの反転対の局所恒等式だけであり、
実際の半核全体の Wronskian 零点や二捩れ点での評価は後続モジュールに残す。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve
open DkMath.Lib.NumberTheory.WeierstrassVeluPair
open DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial

variable {F : Type*} [Field F]

/-- [DkMath.Lib] `xCorrection` の分母を払った多項式分子。

`t = momentT W a`、`u = (2b+a₁a+a₃)^2` と置くと、
`xCorrection = (t(X-a)+u)/(X-a)^2` となる。 -/
noncomputable def xCorrectionNumerator (W : WeierstrassCurve F) (a b : F) : F[X] :=
  C (momentT W a) * (X - C a) + C ((2 * b + W.a₁ * a + W.a₃) ^ 2)

/-- [DkMath.Lib] `xCorrection` の分母多項式。 -/
noncomputable def xCorrectionDenominator (a : F) : F[X] :=
  (X - C a) * (X - C a)

/-- [DkMath.Lib] `zCorrection` に対応する分母を払った微分分子。 -/
noncomputable def zCorrectionNumerator (W : WeierstrassCurve F) (a b : F) : F[X] :=
  -C (momentT W a) * (X - C a) -
    (2 : F[X]) * C ((2 * b + W.a₁ * a + W.a₃) ^ 2)

/-- [DkMath.Lib] x 補正の分子分母は、元の有理式と一致する。

`x ≠ a` なら分母 `(x-a)^2` は非零であり、分母を払った表示を
`xCorrection` の評価へ戻せる。 -/
theorem xCorrection_eq_eval_numerator_div_denominator
    (W : WeierstrassCurve F) {a b x : F} (hxa : x ≠ a) :
    xCorrection W a b x =
      (xCorrectionNumerator W a b).eval x /
        (xCorrectionDenominator a).eval x := by
  simp only [xCorrectionNumerator, xCorrectionDenominator, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, xCorrection]
  field_simp [sub_ne_zero.mpr hxa]

/-- [DkMath.Lib] 一対の補正項の形式微分 Wronskian 恒等式。

分子 `N=t(X-a)+u`、分母 `D=(X-a)^2` に対して

`N' D - N D' = (X-a)(-t(X-a)-2u)`

が成り立つ。右辺の最後の因子が、まさに `zCorrection` の分母を
払った分子である。 -/
theorem xCorrection_numerator_wronskian_eq
    (W : WeierstrassCurve F) (a b : F) :
    (xCorrectionNumerator W a b).derivative * xCorrectionDenominator a -
        xCorrectionNumerator W a b * (xCorrectionDenominator a).derivative =
      (X - C a) * zCorrectionNumerator W a b := by
  simp [xCorrectionNumerator, xCorrectionDenominator, zCorrectionNumerator,
    derivative_mul, derivative_C, derivative_sub, derivative_X,
    derivative_pow, map_add, map_mul]
  ring

/-- [DkMath.Lib] Wronskian 恒等式を有限点で評価した形。

分母非零の点では、評価後の左辺は有理式の分子に対応し、右辺は
`x-a` と z 分子の積になる。半核和の各項へこの等式を適用するための
局所的な教材入口である。 -/
theorem xCorrection_numerator_wronskian_eval
    (W : WeierstrassCurve F) {a b x : F} :
    (xCorrectionNumerator W a b).derivative.eval x *
        (xCorrectionDenominator a).eval x -
        (xCorrectionNumerator W a b).eval x *
          (xCorrectionDenominator a).derivative.eval x =
      (x - a) * (zCorrectionNumerator W a b).eval x := by
  have h := congrArg (fun p : F[X] => p.eval x)
    (xCorrection_numerator_wronskian_eq W a b)
  simpa only [eval_mul, eval_sub, eval_X, eval_C] using h

/-- [DkMath.Lib] 局所 Wronskian を `zCorrection` へ戻す。

`x ≠ a` なら `zCorrection` の分母は `(x-a)^3` であるため、前定理の
分母消去形は

`N'(x)D(x) - N(x)D'(x) = (x-a)^4 zCorrection W a b x`

と書き直せる。この形は、半核和の共通分母を作った後に、二捩れ点での
平方完成座標の消滅を Wronskian の零点へ渡すための直接の局所入力である。 -/
theorem xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection
    (W : WeierstrassCurve F) {a b x : F} (hxa : x ≠ a) :
    (xCorrectionNumerator W a b).derivative.eval x *
        (xCorrectionDenominator a).eval x -
        (xCorrectionNumerator W a b).eval x *
          (xCorrectionDenominator a).derivative.eval x =
      (x - a) ^ 4 * zCorrection W a b x := by
  rw [xCorrection_numerator_wronskian_eval]
  simp [zCorrection, zCorrectionNumerator]
  field_simp [sub_ne_zero.mpr hxa]

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
