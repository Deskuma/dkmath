/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantInput
import DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct
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
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantNormalization
    {α : Type*} : DecidableEq α := Classical.decEq _

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

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] モニック・同次数の標準分母は半核分母に一致する。

分母側の可除性 `G ∣ D_H` に対して、分子側と同じモニック次数比較を適用する。
`D_H` の次数は `veluHalfDenominatorBase_natDegree` から供給できるが、標準分母の
次数比較は呼び出し側の正規化条件として明示的に残す。
-/
theorem veluX_standard_pair_denominator_eq_of_monic
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G)
    (hGmonic : G.Monic)
    (hDmonic : (veluHalfDenominatorBase E H).Monic)
    (hdeg : (veluHalfDenominatorBase E H).natDegree ≤ G.natDegree) :
    G = veluHalfDenominatorBase E H := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hGmonic hDmonic
    (veluX_standard_pair_denominator_dvd E H ho F G hG hrel hcop) hdeg).symm

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準対全体を半核共通対へ同時に正規化する。

分子・分母それぞれのモニック性と次数比較を別々に受け取り、二つの条件付き
一致定理を束ねる。標準対の存在や正規化条件を新たに仮定から導くものではなく、
呼び出し側が供給した条件を一つの監査可能な構造へまとめる入口である。
-/
theorem veluX_standard_pair_eq_of_monic
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
    (hGmonic : G.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hFdeg : (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree)
    (hGdeg : (veluHalfDenominatorBase E H).natDegree ≤ G.natDegree) :
    F = veluHalfNumeratorBase E H ∧
      G = veluHalfDenominatorBase E H := by
  constructor
  · exact veluX_standard_pair_numerator_eq_of_monic E H ho F G hG hrel hcop hF hA hFdeg
  · exact veluX_standard_pair_denominator_eq_of_monic E H ho F G hG hrel hcop hGmonic hD hGdeg

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準対の Wronskian を半核対の Wronskian へ輸送する。

標準対全体の条件付き正規化を一度適用し、`wronskian` の定義域を変更せずに
多項式対の一致をそのまま微分不変量へ輸送する。二捩れ根の幾何学的証明は
別モジュールに残し、この定理は係数対の境界だけを担当する。
-/
theorem veluX_standard_pair_wronskian_eq_base_of_monic
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G)
    (hF : F.Monic) (hGmonic : G.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hFdeg : (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree)
    (hGdeg : (veluHalfDenominatorBase E H).natDegree ≤ G.natDegree) :
    wronskian F G =
      wronskian (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H) := by
  obtain ⟨hF_eq, hG_eq⟩ := veluX_standard_pair_eq_of_monic E H ho F G hG hrel hcop
    hF hGmonic hA hD hFdeg hGdeg
  rw [hF_eq, hG_eq]

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 正規化された標準分母は核外平行移動点で非零である。

`veluHalfDenominatorBase_eval_ne_zero_translation` が有限積分母の非衝突を
供給し、前定理の分母一致を通じて標準分母 `G` へ輸送する。これは点評価で
標準表示を使う際の正則性を、モニック正規化の仮定から明示的に取り出す補題である。
-/
theorem veluX_standard_pair_denominator_eval_ne_zero_of_monic
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G)
    (hF : F.Monic) (hGmonic : G.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hFdeg : (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree)
    (hGdeg : (veluHalfDenominatorBase E H).natDegree ≤ G.natDegree)
    (P : Points E) (hP : P ∉ H) (Q : H) :
    G.eval (P + Q.val).xc ≠ 0 := by
  obtain ⟨_, hG_eq⟩ := veluX_standard_pair_eq_of_monic E H ho F G hG hrel hcop
    hF hGmonic hA hD hFdeg hGdeg
  rw [hG_eq]
  exact veluHalfDenominatorBase_eval_ne_zero_translation E H P hP Q

omit [CharZero K] in
/-- [DkMath.Lib] 標準 Wronskian の二捩れ平行移動根を正規化経路で得る。

標準対を半核共通対へ正規化してから、既存の半核側二捩れ根定理を適用する。
従って、この定理が新たに証明する幾何学は半核側のものではなく、標準表示の
モニック性・次数条件の下で、その根を標準 Wronskian へ確実に輸送する境界である。
-/
theorem veluX_standard_pair_wronskian_root_of_monic_normalization
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hcop : IsCoprime F G)
    (hF : F.Monic) (hGmonic : G.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hFdeg : (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree)
    (hGdeg : (veluHalfDenominatorBase E H).natDegree ≤ G.natDegree)
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0) :
    (wronskian F G).IsRoot (P + Q.val).xc := by
  obtain ⟨hF_eq, hG_eq⟩ := veluX_standard_pair_eq_of_monic E H ho F G hG hrel hcop
    hF hGmonic hA hD hFdeg hGdeg
  rw [hF_eq, hG_eq]
  exact veluHalf_base_wronskian_root_of_odd_twoTorsion E H ho P hP hneg Q hQ

omit [CharZero K] in
/-- [DkMath.Lib] 正規化標準対から有限ファイバー因子分解へ進む終端。

`fiberPolynomial` のモニック性・次数上界と、標準対のモニック正規化条件を
明示的に仮定する。各半核代表の Wronskian 根は前定理で生成し、既存の
`eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_wronskian_roots` に渡す。
したがって、ここで新たに導入されるのは有限ファイバーへの接続だけであり、
ファイバーのモニック性や次数評価を無条件に供給するものではない。
-/
theorem eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_monic_normalization
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (F G : (AlgebraicClosure K)[X]) (hcoprime : IsCoprime F G) (hG : G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (c : AlgebraicClosure K)
    (hp : (fiberPolynomial F G c).Monic)
    (hPc : kernelXAt E H P hP = c)
    (hF : F.Monic) (hGmonic : G.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hFdeg : (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree)
    (hGdeg : (veluHalfDenominatorBase E H).natDegree ≤ G.natDegree)
    (hdeg : (fiberPolynomial F G c).natDegree ≤ Nat.card H) :
    fiberPolynomial F G c =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
        (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  have hGaeval : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0 := by
    intro hzero
    exact hG ((transcendental_iff.mp
      (genericX_transcendental_for_wronskian E)) G hzero)
  have hwronskian : ∀ Q : halfKernel E H,
      (wronskian F G).IsRoot ((P + Q.val.val).xc) := by
    intro Q
    have hQ : Q.val ≠ 0 := ((mem_halfKernel E H Q.val).mp Q.property).1
    exact veluX_standard_pair_wronskian_root_of_monic_normalization
      E H ho F G hGaeval hrel hcoprime hF hGmonic hA hD hFdeg hGdeg
      P hP hneg Q.val hQ
  exact eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_wronskian_roots
    E H ho P hP hneg F G hcoprime hG hrel c hp hPc hwronskian hdeg

end DkMath.Lib.NumberTheory.EllipticFiniteKernel

