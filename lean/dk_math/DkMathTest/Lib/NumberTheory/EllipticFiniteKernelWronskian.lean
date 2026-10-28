/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianAssembly

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
open DkMath.Lib.Algebra.FiniteProductWronskian

variable {F ι : Type*} [Field F] [DecidableEq ι]

example (W : WeierstrassCurve F) {a b x : F} (hxa : x ≠ a) :
    (xCorrectionNumerator W a b).derivative.eval x *
        (xCorrectionDenominator a).eval x -
        (xCorrectionNumerator W a b).eval x *
          (xCorrectionDenominator a).derivative.eval x =
      (x - a) ^ 4 * zCorrection W a b x :=
  xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection W hxa

example (s : Finset ι) (W : WeierstrassCurve F) (a b : ι → F) :
    (commonNumerator s
        (fun i => xCorrectionNumerator W (a i) (b i))
        (fun i => xCorrectionDenominator (a i))).derivative *
        commonDenominator s (fun i => xCorrectionDenominator (a i)) -
      commonNumerator s
          (fun i => xCorrectionNumerator W (a i) (b i))
          (fun i => xCorrectionDenominator (a i)) *
        (commonDenominator s (fun i => xCorrectionDenominator (a i))).derivative =
      (commonDenominator s (fun i => xCorrectionDenominator (a i))) ^ 2 +
        ∑ i ∈ s,
          (erasedProduct s (fun j => xCorrectionDenominator (a j)) i) ^ 2 *
            ((X - C (a i)) * zCorrectionNumerator W (a i) (b i)) :=
  finite_xCorrection_wronskian_eq s W a b

example (s : Finset ι) (W : WeierstrassCurve F) (a b : ι → F) (x : F)
    (hxa : ∀ i ∈ s, x ≠ a i) :
    ((commonNumerator s
        (fun i => xCorrectionNumerator W (a i) (b i))
        (fun i => xCorrectionDenominator (a i))).derivative.eval x *
        (commonDenominator s (fun i => xCorrectionDenominator (a i))).eval x -
      (commonNumerator s
          (fun i => xCorrectionNumerator W (a i) (b i))
          (fun i => xCorrectionDenominator (a i))).eval x *
        (commonDenominator s (fun i => xCorrectionDenominator (a i))).derivative.eval x) =
      (commonDenominator s (fun i => xCorrectionDenominator (a i))).eval x ^ 2 *
        (1 + ∑ i ∈ s, zCorrection W (a i) (b i) x) :=
  finite_xCorrection_wronskian_eval_eq_denominator_sq_mul_one_add_z s W a b x hxa

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection

end DkMathTest.EllipticFiniteKernelWronskian
