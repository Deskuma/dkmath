/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantInput
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization"

/-!
# 標準 `RatFunc` 対から半核多項式への正規化

`veluX_standard_pair_cross_relation` は、標準分子分母 `F,G` と有限積から作った
半核分子分母 `A_H,D_H` の間に

`F * D_H = A_H * G`

という交差乗算を与える。本モジュールは、この恒等式を `IsCoprime F G` と
組み合わせ、まず `F ∣ A_H` と `G ∣ D_H` を取り出す。さらに両方の対が
モニックで次数が揃う場合に限り、`F = A_H` まで正規化する。

ここでは標準対の存在・モニック性・次数一致は仮定として受け取る。したがって、
この層は係数体の同一性を新たに証明するものではなく、既存の関数体表示を
安全に多項式の可除性へ輸送する教科書的な橋である。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open DkMath.Lib.Algebra
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.Algebra.RationalPolynomialFiber

variable {K : Type*} [Field K] [CharZero K] [NeZero (2 : K)]

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準分子は半核共通分子を割り切る。

交差乗算 `F * D_H = A_H * G` と `IsCoprime F G` から、有限積分子への
可除性だけを抽出する。標準分子と半核分子の同一性には、別途モニック性と
次数比較が必要である。
-/
theorem veluX_standard_pair_numerator_dvd
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G) :
    F ∣ veluHalfNumeratorBase E H := by
  apply dvd_of_cross_relation_of_coprime hcop
  exact veluX_standard_pair_cross_relation E H ho F G hG hrel

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準分母は半核共通分母を割り切る。

同じ交差乗算を今度は `G ∣ F * D_H` と読み替え、`IsCoprime G F` の
Euclid 型補題を適用する。分子側と分母側の可除性を対称に保持することで、
後続の正規化で片側だけを誤って固定することを防ぐ。
-/
theorem veluX_standard_pair_denominator_dvd
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G) :
    G ∣ veluHalfDenominatorBase E H := by
  have hcross := veluX_standard_pair_cross_relation E H ho F G hG hrel
  apply hcop.symm.dvd_of_dvd_mul_left
  rw [hcross]
  exact dvd_mul_left _ _

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] モニック・同次数の標準分子は半核分子に一致する。

前定理の `F ∣ A_H` と、両者のモニック性および
`A_H.natDegree ≤ F.natDegree` を `eq_of_monic_of_dvd_of_natDegree_le` に渡す。
ここで次数仮定を明示的に残すことが、未証明の標準対正規化を隠さないための要点である。
-/
theorem veluX_standard_pair_numerator_eq_of_monic
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G)
    (hF : F.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hdeg : (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree) :
    F = veluHalfNumeratorBase E H := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hF hA
    (veluX_standard_pair_numerator_dvd E H ho F G hG hrel hcop) hdeg).symm

end DkMath.Lib.NumberTheory.EllipticFiniteKernel

