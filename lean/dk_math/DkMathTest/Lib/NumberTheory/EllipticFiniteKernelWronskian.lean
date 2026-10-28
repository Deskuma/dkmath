/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianAssembly
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianHalf

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskian"

/-!
# Wronskian 局所恒等式の回帰入口

ここでは具体的な核や曲線を固定せず、公開された局所定理をそのまま
再利用できることを確認する。二捩れ点での幾何学的零点はまだ別入力だが、
Vélu 一対補正の分母消去 Wronskian はこの API から呼び出せる。
-/
namespace DkMathTest.EllipticFiniteKernelWronskian

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.WeierstrassVeluPair
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
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

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) [E.IsElliptic] :
    veluX E H =
      (veluHalfNumerator E H).eval (genericX E (AlgebraicClosure F)) /
        (veluHalfDenominator E H).eval (genericX E (AlgebraicClosure F)) :=
  veluX_eq_veluHalfNumerator_div_denominator E H ho

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_denominator_factor_ne_zero
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_eq_veluHalfNumerator_div_denominator

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) [E.IsElliptic] :
    let F' := (E.toAffine⁄(AlgebraicClosure F)).FunctionField
    let W := E.map (algebraMap F F')
    let x := genericX E (AlgebraicClosure F)
    let z := 2 * genericY E (AlgebraicClosure F) + W.a₁ * x + W.a₃
    (veluHalfDenominator E H).eval x ^ 2 *
        (2 * veluY E H + W.a₁ * veluX E H + W.a₃) =
      z * ((veluHalfNumerator E H).derivative.eval x *
          (veluHalfDenominator E H).eval x -
        (veluHalfNumerator E H).eval x *
          (veluHalfDenominator E H).derivative.eval x) :=
  veluHalf_denominator_sq_mul_z_eq_z_mul_wronskian E H ho

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_denominator_sq_mul_z_eq_z_mul_wronskian

end DkMathTest.EllipticFiniteKernelWronskian
