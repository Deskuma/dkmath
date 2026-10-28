/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskian

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskian"

/-!
# Wronskian 局所恒等式の回帰入口

ここでは具体的な核や曲線を固定せず、公開された局所定理をそのまま
再利用できることを確認する。二捩れ点での幾何学的零点はまだ別入力だが、
Vélu 一対補正の分母消去 Wronskian はこの API から呼び出せる。
-/
namespace DkMathTest.EllipticFiniteKernelWronskian

open Polynomial
open WeierstrassCurve
open DkMath.Lib.NumberTheory.WeierstrassVeluPair
open DkMath.Lib.NumberTheory.EllipticFiniteKernel

variable {F : Type*} [Field F]

example (W : WeierstrassCurve F) {a b x : F} (hxa : x ≠ a) :
    (xCorrectionNumerator W a b).derivative.eval x *
        (xCorrectionDenominator a).eval x -
        (xCorrectionNumerator W a b).eval x *
          (xCorrectionDenominator a).derivative.eval x =
      (x - a) ^ 4 * zCorrection W a b x :=
  xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection W hxa

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection

end DkMathTest.EllipticFiniteKernelWronskian
