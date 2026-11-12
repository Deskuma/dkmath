/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianAssembly
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianHalf
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBase
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization
import DkMath.Lib.Algebra.WronskianCrossMultiplication

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
open DkMath.Lib.NumberTheory.EllipticPointEvaluation
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.Algebra

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

/-! 係数体ブリッジの回帰例。`A_H,D_H` は代数閉包係数で作ってから、
関数体係数の既存 Vélu 表示へ `Polynomial.map` で送れる。 -/

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H] :
    let F' := (E.toAffine⁄(AlgebraicClosure F)).FunctionField
    let c := algebraMap (AlgebraicClosure F) F'
    Polynomial.map c (veluHalfNumeratorBase E H) = veluHalfNumerator E H :=
  map_veluHalfNumeratorBase E H

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H] :
    let F' := (E.toAffine⁄(AlgebraicClosure F)).FunctionField
    let c := algebraMap (AlgebraicClosure F) F'
    Polynomial.map c (veluHalfDenominatorBase E H) = veluHalfDenominator E H :=
  map_veluHalfDenominatorBase E H

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.map_veluHalfNumeratorBase
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.map_veluHalfDenominatorBase

example {R S : Type*} [Field R] [Field S] (f : R →+* S)
    (P Q : R[X]) :
    Polynomial.map f (wronskian P Q) =
      wronskian (Polynomial.map f P) (Polynomial.map f Q) :=
  map_wronskian f P Q

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.map_wronskian

/-! 二捩れ局所特殊化の回帰例。源側の平方完成座標の非零性と、
標的側での零性を別々の補題として再利用できることを確認する。 -/

variable [NeZero (2 : F)]

example (E : WeierstrassCurve F) (P : Points E) (hP : P ≠ 0)
    (hz : 2 * P.yc + (E⁄(AlgebraicClosure F)).a₁ * P.xc +
      (E⁄(AlgebraicClosure F)).a₃ = 0) :
    -P = P :=
  eq_neg_of_completedSquare_eq_zero E P hP hz

example (E : WeierstrassCurve F) (P : Points E) (hP : P ≠ 0)
    (hneg : -P ≠ P) :
    2 * P.yc + (E⁄(AlgebraicClosure F)).a₁ * P.xc +
      (E⁄(AlgebraicClosure F)).a₃ ≠ 0 :=
  completedSquare_ne_zero_of_neg_ne E P hP hneg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) :
    2 * kernelYAt E H P hP + (kernelModel E H).a₁ * kernelXAt E H P hP +
      (kernelModel E H).a₃ = 0 :=
  kernelAt_completedSquare_eq_zero_of_neg_fixed E H P hP hneg

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E))
    (P : Points E) (hP : P ∉ H) (Q : H)
    (hneg : -(P + Q.val) ≠ P + Q.val) :
    2 * (P + Q.val).yc + (E⁄(AlgebraicClosure F)).a₁ * (P + Q.val).xc +
      (E⁄(AlgebraicClosure F)).a₃ ≠ 0 :=
  completedSquare_ne_zero_of_neg_ne_translation E H P hP Q hneg

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E))
    (hodd : Odd (Nat.card H)) (P : Points E) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0) :
    -(P + Q.val) ≠ P + Q.val :=
  neg_ne_of_odd_kernel_twoTorsion_translate E H hodd P hneg Q hQ

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H)
    (hnegTranslation : -(P + Q.val) ≠ P + Q.val) :
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure F)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure F)).a₃ ≠ 0) ∧
      (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0) :=
  completedSquare_translation_pair E H P hP hneg Q hnegTranslation

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0) :
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure F)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure F)).a₃ ≠ 0) ∧
      (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0) :=
  completedSquare_translation_pair_of_odd_kernel E H hodd P hP hneg Q hQ

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (R : Points E) (hcollision : ∀ Q : halfKernel E H,
      R.xc ≠ Q.val.val.xc) :
    (veluHalfDenominatorBase E H).eval R.xc ≠ 0 :=
  veluHalfDenominatorBase_eval_ne_zero E H R hcollision

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) (S : halfKernel E H) :
    (P + Q.val).xc ≠ S.val.val.xc :=
  translated_x_ne_halfKernel_of_kernel_outside E H P hP Q S

example (E : WeierstrassCurve F) (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) :
    (veluHalfDenominatorBase E H).eval (P + Q.val).xc ≠ 0 :=
  veluHalfDenominatorBase_eval_ne_zero_translation E H P hP Q

example (E : WeierstrassCurve F) [E.IsElliptic] :
    Transcendental (AlgebraicClosure F) (genericX E (AlgebraicClosure F)) :=
  genericX_transcendental_for_wronskian E

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H] :
    Polynomial.aeval (genericX E (AlgebraicClosure F))
      (veluHalfDenominatorBase E H) ≠ 0 :=
  veluHalfDenominatorBase_eval_genericX_ne_zero E H

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F))
        (veluHalfNumeratorBase E H) /
        Polynomial.aeval (genericX E (AlgebraicClosure F))
          (veluHalfDenominatorBase E H) :=
  veluX_eq_veluHalfNumeratorBase_div_denominator E H ho

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q) :
    P * veluHalfDenominatorBase E H = veluHalfNumeratorBase E H * Q :=
  veluX_standard_pair_cross_relation E H ho P Q hQ hrel

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P QF : (AlgebraicClosure F)[X])
    (hQF : Polynomial.aeval (genericX E (AlgebraicClosure F)) QF ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) QF)
    (T : Points E) (hT : T ∉ H) (Q : H)
    (hbase :
      (wronskian (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H)).IsRoot (T + Q.val).xc) :
    (wronskian P QF).IsRoot (T + Q.val).xc :=
  veluX_standard_pair_wronskian_root_of_translation E H ho P QF hQF hrel T hT Q hbase

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (Q : H) (hQ : Q ≠ 0)
    (hidentity :
      (veluHalfDenominatorBase E H).eval (T + Q.val).xc ^ 2 *
          (2 * kernelYAt E H (T + Q.val) (add_not_mem_kernel E H T hT Q) +
            (kernelModel E H).a₁ * kernelXAt E H (T + Q.val)
              (add_not_mem_kernel E H T hT Q) + (kernelModel E H).a₃) =
        (2 * (T + Q.val).yc + (E⁄(AlgebraicClosure F)).a₁ * (T + Q.val).xc +
            (E⁄(AlgebraicClosure F)).a₃) *
          (wronskian (veluHalfNumeratorBase E H)
            (veluHalfDenominatorBase E H)).eval (T + Q.val).xc) :
    (wronskian (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).IsRoot (T + Q.val).xc :=
  veluHalf_base_wronskian_root_of_cleared_identity E H ho T hT hneg Q hQ hidentity

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (Q : H) (hQ : Q ≠ 0) :
    (wronskian (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).IsRoot (T + Q.val).xc :=
  veluHalf_base_wronskian_root_of_odd_twoTorsion E H ho T hT hneg Q hQ

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P QF : (AlgebraicClosure F)[X])
    (hQF : Polynomial.aeval (genericX E (AlgebraicClosure F)) QF ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) QF)
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (Q : H) (hQ : Q ≠ 0) :
    (wronskian P QF).IsRoot (T + Q.val).xc :=
  veluX_standard_pair_wronskian_root_of_odd_twoTorsion E H ho P QF hQF hrel T hT hneg Q hQ

example (E : WeierstrassCurve F) [E.IsElliptic]
    (T : Points E) (hT : T ≠ 0) (p : (AlgebraicClosure F)[X]) :
    pointValuation E T
        (Polynomial.aeval (genericX E (AlgebraicClosure F)) p) ≤ 1 :=
  pointValuation_aeval_le_one E T hT p

example (E : WeierstrassCurve F) [E.IsElliptic]
    (T : Points E) (hT : T ≠ 0) (p : (AlgebraicClosure F)[X]) :
    value E T (Polynomial.aeval (genericX E (AlgebraicClosure F)) p)
        (pointValuation_aeval_le_one E T hT p) = p.eval T.xc :=
  value_aeval_eq_eval E T hT p

example (E : WeierstrassCurve F) [E.IsElliptic]
    (T : Points E) (hT : T ≠ 0) (p : (AlgebraicClosure F)[X]) :
    (pointValuation E T).Cong
      (Polynomial.aeval (genericX E (AlgebraicClosure F)) p)
      (algebraMap _ _ (p.eval T.xc)) :=
  pointValuation_aeval_congr_eval E T hT p

example (E : WeierstrassCurve F) [E.IsElliptic]
    (T : Points E)
    (d dp a ap z zH : AlgebraicClosure F)
    (fD fDp fA fAp fZ fZH :
      (E.toAffine⁄(AlgebraicClosure F)).FunctionField)
    (hD : pointValuation E T fD ≤ 1)
    (hDp : pointValuation E T fDp ≤ 1)
    (hA : pointValuation E T fA ≤ 1)
    (hAp : pointValuation E T fAp ≤ 1)
    (hZ : pointValuation E T fZ ≤ 1)
    (hZH : pointValuation E T fZH ≤ 1)
    (hDval : (pointValuation E T).Cong fD (algebraMap _ _ d))
    (hDpval : (pointValuation E T).Cong fDp (algebraMap _ _ dp))
    (hAval : (pointValuation E T).Cong fA (algebraMap _ _ a))
    (hApval : (pointValuation E T).Cong fAp (algebraMap _ _ ap))
    (hZval : (pointValuation E T).Cong fZ (algebraMap _ _ z))
    (hZHval : (pointValuation E T).Cong fZH (algebraMap _ _ zH))
    (hidentity : fD ^ 2 * fZH = fZ * (fAp * fD - fA * fDp)) :
    d ^ 2 * zH = z * (ap * d - a * dp) :=
  evalHom_cleared_identity E T d dp a ap z zH fD fDp fA fAp fZ fZH
    hD hDp hA hAp hZ hZH hDval hDpval hAval hApval hZval hZHval hidentity

/-! 関数体恒等式を基礎係数対へ戻し、核外の有限点で正則評価する
教科書経路の回帰例。 -/

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    let F' := (E.toAffine⁄(AlgebraicClosure F)).FunctionField
    let W := E.map (algebraMap F F')
    let x := genericX E (AlgebraicClosure F)
    let z := 2 * genericY E (AlgebraicClosure F) + W.a₁ * x + W.a₃
    (Polynomial.aeval x (veluHalfDenominatorBase E H)) ^ 2 *
        (2 * veluY E H + W.a₁ * veluX E H + W.a₃) =
      z * (Polynomial.aeval x (derivative (veluHalfNumeratorBase E H)) *
          Polynomial.aeval x (veluHalfDenominatorBase E H) -
        Polynomial.aeval x (veluHalfNumeratorBase E H) *
          Polynomial.aeval x (derivative (veluHalfDenominatorBase E H))) :=
  veluHalf_base_cleared_identity_function_field E H ho

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (R : Points E) (hR : R ∉ H) :
    (veluHalfDenominatorBase E H).eval R.xc ^ 2 *
        (2 * kernelYAt E H R hR +
          (kernelModel E H).a₁ * kernelXAt E H R hR +
          (kernelModel E H).a₃) =
      (2 * R.yc + (E⁄(AlgebraicClosure F)).a₁ * R.xc +
        (E⁄(AlgebraicClosure F)).a₃) *
        (wronskian (veluHalfNumeratorBase E H)
          (veluHalfDenominatorBase E H)).eval R.xc :=
  veluHalf_cleared_identity_at_kernel_outside E H ho R hR

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.eq_neg_of_completedSquare_eq_zero
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.completedSquare_ne_zero_of_neg_ne
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.kernelAt_completedSquare_eq_zero_of_neg_fixed
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.completedSquare_ne_zero_of_neg_ne_translation
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.neg_ne_of_odd_kernel_twoTorsion_translate
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.completedSquare_translation_pair
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.completedSquare_translation_pair_of_odd_kernel
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_ne_zero
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.translated_x_ne_halfKernel_of_kernel_outside
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_ne_zero_translation
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.genericX_transcendental_for_wronskian
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalfDenominatorBase_eval_genericX_ne_zero
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_eq_veluHalfNumeratorBase_div_denominator
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_cross_relation
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_wronskian_root_of_translation
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_wronskian_root_of_cleared_identity
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_wronskian_root_of_odd_twoTorsion
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_wronskian_root_of_odd_twoTorsion
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.pointValuation_aeval_le_one
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.value_aeval_eq_eval
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.pointValuation_aeval_congr_eval
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.evalHom_cleared_identity
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_cleared_identity_function_field
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_cleared_identity_at_kernel_outside

example {F : Type*} [Field F] (A D P Q : F[X]) (hcross : A * D = P * Q) :
    wronskian A Q * D ^ 2 = wronskian P D * Q ^ 2 :=
  wronskian_mul_denominator_sq_eq A Q P D hcross

example {F : Type*} [Field F] (A D P Q : F[X]) (x : F)
    (hcross : A * D = P * Q) (hD : D.eval x ≠ 0)
    (hAD : (wronskian P D).IsRoot x) :
    (wronskian A Q).IsRoot x :=
  wronskian_isRoot_of_cross_relation A Q P D x hcross hD hAD

example {F : Type*} [Field F] (A D P Q : F[X]) (x : F)
    (hcross : A * D = P * Q) (hQ : Q.eval x ≠ 0)
    (hAQ : (wronskian A Q).IsRoot x) :
    (wronskian P D).IsRoot x :=
  wronskian_isRoot_of_cross_relation_rev A Q P D x hcross hQ hAQ

example {F : Type*} [Field F] (A D : F[X]) (x z zH : F)
    (hidentity : D.eval x ^ 2 * zH = z * (wronskian A D).eval x)
    (hz : z ≠ 0) (hzH : zH = 0) :
    (wronskian A D).IsRoot x :=
  wronskian_isRoot_of_denominator_cleared_identity A D x z zH hidentity hz hzH

example {R S : Type*} [Field R] [Field S] [Algebra R S]
    (A D F G : R[X]) (x : S) (hx : Transcendental R x)
    (hG : Polynomial.aeval x G ≠ 0) (hD : Polynomial.aeval x D ≠ 0)
    (hrel : Polynomial.aeval x F / Polynomial.aeval x G =
      Polynomial.aeval x A / Polynomial.aeval x D) :
    F * D = A * G :=
  cross_relation_of_aeval_div_eq F G A D x hx hG hD hrel

#print axioms DkMath.Lib.Algebra.wronskian_mul_denominator_sq_eq
#print axioms DkMath.Lib.Algebra.wronskian_isRoot_of_cross_relation
#print axioms DkMath.Lib.Algebra.wronskian_isRoot_of_cross_relation_rev
#print axioms DkMath.Lib.Algebra.wronskian_isRoot_of_denominator_cleared_identity
#print axioms DkMath.Lib.Algebra.cross_relation_of_aeval_div_eq

end DkMathTest.EllipticFiniteKernelWronskian
