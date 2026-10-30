/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantInput
import DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBifurcation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization
import DkMath.Lib.Algebra.PolynomialProportional

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

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 半核共通分子・分母は互いに素である。

無限遠点で選んだ標準対 `(F,G)` の存在だけを使い、交差乗算から半核対が
標準対の共通非零スカラー倍になることを一般補題で取り出す。その後、単位倍
による `IsCoprime` の不変性を適用する。標準対との完全一致やモニック性は要求しない。
-/
theorem veluHalf_base_isCoprime
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    IsCoprime (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H) := by
  obtain ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, _⟩ :=
    exists_veluX_fixed_pair_factorization E H ho
  have hGaeval : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0 := by
    intro hzero
    exact hG ((transcendental_iff.mp
      (genericX_transcendental_for_wronskian E)) G hzero)
  have hcross := veluX_standard_pair_cross_relation E H ho F G hGaeval hrel
  have hFne : F ≠ 0 := by
    intro hFzero
    have hFnat : F.natDegree = 0 := by simp [hFzero]
    omega
  have hAne : veluHalfNumeratorBase E H ≠ 0 :=
    (veluHalfNumeratorBase_monic E H).ne_zero
  have hAdeg : (veluHalfNumeratorBase E H).natDegree = Nat.card H := by
    calc
      (veluHalfNumeratorBase E H).natDegree =
          1 + 2 * (halfKernel E H).card := veluHalfNumeratorBase_natDegree E H
      _ = 2 * (halfKernel E H).card + 1 := by omega
      _ = Nat.card H := card_halfKernel E H ho
  obtain ⟨u, hu, hAeq, hDeq⟩ := proportional_of_cross_relation_of_coprime
    hcop hFne hAne hcross (by omega :
      (veluHalfNumeratorBase E H).natDegree ≤ F.natDegree)
  have huPoly : IsUnit (Polynomial.C u) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu)
  rw [hAeq, hDeq]
  exact (isCoprime_mul_units_left huPoly huPoly F G).mpr hcop

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準 `RatFunc` 対を半核対の共通非零スカラー倍へ戻す。

標準対 `(F,G)` の交差乗算と互いに素性を、半核対 `(A_H,D_H)` を第一の対として
`proportional_of_cross_relation_of_coprime` に渡す。標準分子の次数は半核分子と
同じ `Nat.card H` なので商の次数が零となり、
`F = C u * A_H`, `G = C u * D_H` を得る。これはモニック性を仮定せずに
係数対の正規化自由度を明示する橋であり、後続の判別式・ファイバー輸送が
「単位倍を除けば半核対である」ことを直接利用できるようにする。 -/
theorem veluX_standard_pair_proportional_to_veluHalf_base
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hFdeg : F.natDegree = Nat.card H) :
    ∃ u : AlgebraicClosure K, u ≠ 0 ∧
      F = Polynomial.C u * veluHalfNumeratorBase E H ∧
      G = Polynomial.C u * veluHalfDenominatorBase E H := by
  have hAne : veluHalfNumeratorBase E H ≠ 0 :=
    (veluHalfNumeratorBase_monic E H).ne_zero
  have hFne : F ≠ 0 := by
    intro hF
    have : F.natDegree = 0 := by simp [hF]
    rw [hFdeg] at this
    exact (Nat.ne_of_gt Nat.card_pos) this
  have hcross := veluX_standard_pair_cross_relation E H ho F G hG hrel
  have hAdeg : F.natDegree ≤
      (veluHalfNumeratorBase E H).natDegree := by
    rw [hFdeg]
    calc
      Nat.card H = 1 + 2 * (halfKernel E H).card := by
        symm
        rw [← card_halfKernel E H ho]
        omega
      _ = (veluHalfNumeratorBase E H).natDegree :=
        (veluHalfNumeratorBase_natDegree E H).symm
      _ ≤ (veluHalfNumeratorBase E H).natDegree := le_rfl
  exact proportional_of_cross_relation_of_coprime
    (veluHalf_base_isCoprime E H ho) hAne hFne hcross.symm hAdeg

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準対のファイバーを半核対のファイバーへ輸送する。

前定理の共通スカラー倍 `F = C u * A_H`, `G = C u * D_H` は、各ファイバー
`F-cG` に同じ `C u` を因子として持たせる。ここでは割り算を使わず、
`fiberPolynomial` の定義を展開して可換環の分配法則だけで
`fiberPolynomial F G c = C u * fiberPolynomial A_H D_H c` を固定する。
判別式を直接比較する前段として、単位倍の影響を一箇所に隔離する教科書的橋である。
-/
theorem fiberPolynomial_eq_C_mul_of_proportional
    {A D F G : (AlgebraicClosure K)[X]} {u c : AlgebraicClosure K}
    (hF : F = Polynomial.C u * A)
    (hG : G = Polynomial.C u * D) :
    fiberPolynomial F G c = Polynomial.C u * fiberPolynomial A D c := by
  rw [fiberPolynomial, fiberPolynomial, hF, hG]
  simp only [mul_sub]
  ring

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 共通非零スカラー倍はファイバーの正規化を変えない。

`normalize` は多項式の単元倍を同じ代表へ送る。従って標準対と半核対の
ファイバーが `C u` 倍で一致するなら、非零 `u` のもとで正規化ファイバーも
一致する。これは根積の形を直接比較する際に、係数対の選択依存性を消す最後の
代数的整理である。
-/
theorem normalize_fiberPolynomial_eq_of_proportional
    {A D F G : (AlgebraicClosure K)[X]} {u c : AlgebraicClosure K}
    (hu : u ≠ 0)
    (hF : F = Polynomial.C u * A)
    (hG : G = Polynomial.C u * D) :
    normalize (fiberPolynomial F G c) = normalize (fiberPolynomial A D c) := by
  rw [fiberPolynomial_eq_C_mul_of_proportional hF hG]
  apply normalize_eq_normalize_iff_associated.mpr
  exact associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu))

/-- [DkMath.Lib] 半核対を直接用いた特殊ファイバー因子分解。

`veluX` の明示的半核表示、半核対の互いに素性、奇数核二捩れ枝の Wronskian 根を
既存の有限ファイバー終端へまとめて渡す。標準 `RatFunc` 対の完全一致を経由しない
短縮経路であり、ファイバーのモニック性と次数上界は呼び出し側に残す。
-/
theorem veluHalf_base_special_fiber
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c)
    (hp : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).Monic)
    (hdeg : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).natDegree ≤ Nat.card H) :
    fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
        (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  have hcop := veluHalf_base_isCoprime E H ho
  have hD : veluHalfDenominatorBase E H ≠ 0 :=
    (veluHalfDenominatorBase_monic E H).ne_zero
  have hrel := veluX_eq_veluHalfNumeratorBase_div_denominator E H ho
  have hwronskian : ∀ Q : halfKernel E H,
      (wronskian (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H)).IsRoot ((P + Q.val.val).xc) := by
    intro Q
    have hQ : Q.val ≠ 0 := ((mem_halfKernel E H Q.val).mp Q.property).1
    exact veluHalf_base_wronskian_root_of_odd_twoTorsion E H ho P hP hneg Q.val hQ
  exact eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_wronskian_roots
    E H ho P hP hneg (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) hcop hD hrel c hp hPc hwronskian hdeg

/-- [DkMath.Lib] 半核対の次数公式から特殊ファイバーの正規化条件を供給する。

前定理では、ファイバー多項式のモニック性と次数上界を呼び出し側から受け取った。
ここではその二つを追加仮定にせず、`veluHalfNumeratorBase` のモニック性・次数、
`veluHalfDenominatorBase` の次数、および `card_halfKernel` から自動的に導く。
従って残る入力は、奇数核、核外二捩れ点、そしてその点での有限値だけである。
数学的には `D_H` の次数が `A_H` より小さいため、任意の有限値 `c` に対して
`A_H - c D_H` は主項を失わずモニックであり、次数は `Nat.card H` に固定される。 -/
theorem veluHalf_base_special_fiber_of_odd_twoTorsion
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
        (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  have hAmonic := veluHalfNumeratorBase_monic E H
  have hDdeg : (veluHalfDenominatorBase E H).natDegree =
      2 * (halfKernel E H).card := veluHalfDenominatorBase_natDegree E H
  have hAdeg : (veluHalfNumeratorBase E H).natDegree = Nat.card H := by
    calc
      (veluHalfNumeratorBase E H).natDegree =
          1 + 2 * (halfKernel E H).card := veluHalfNumeratorBase_natDegree E H
      _ = 2 * (halfKernel E H).card + 1 := by omega
      _ = Nat.card H := card_halfKernel E H ho
  have hDlt : (veluHalfDenominatorBase E H).natDegree <
      (veluHalfNumeratorBase E H).natDegree := by
    rw [hDdeg, hAdeg]
    have hc := card_halfKernel E H ho
    omega
  have hqdeg : (C c * veluHalfDenominatorBase E H).natDegree <
      (veluHalfNumeratorBase E H).natDegree :=
    (natDegree_C_mul_le c (veluHalfDenominatorBase E H)).trans_lt hDlt
  have hp : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).Monic := by
    unfold fiberPolynomial
    exact hAmonic.sub_of_left (degree_lt_degree hqdeg)
  have hdeg : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).natDegree ≤ Nat.card H := by
    rw [fiberPolynomial_natDegree_eq_of_natDegree_lt hDlt, hAdeg]
  exact veluHalf_base_special_fiber E H ho P hP hneg c hPc hp hdeg

/-- [DkMath.Lib] 特殊ファイバーを任意の有限 x 値で評価した根差積公式。

二捩れ代表 `P` における半核ファイバー因子分解を `fiberFactor_eval` へ渡し、
`A_H-cD_H` の評価を、単純根 `P.xc` と半核移動点の距離積の平方へ展開する。
これは判別式積の `pair_relation` に必要な局所評価の直接入力であり、まだ別の
二捩れ点における `kernelXAt` の値との商関係は仮定しない。
-/
theorem veluHalf_base_special_fiber_eval_eq_root_distance_product_sq
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c)
    (e : AlgebraicClosure K) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).eval e =
      (e - P.xc) *
        (∏ Q : halfKernel E H,
          (e - (P + Q.val.val).xc)) ^ 2 := by
  rw [veluHalf_base_special_fiber_of_odd_twoTorsion E H ho P hP hneg c hPc]
  simpa using
    (fiberFactor_eval (Finset.univ : Finset (halfKernel E H)) P.xc e
      (fun Q : halfKernel E H => (P + Q.val.val).xc))

omit [CharZero K] [NeZero (2 : K)] in
/--
[DkMath.Lib] 特殊ファイバー評価を `X_H-c` の値へ戻す。

 `veluHalf_base_special_fiber_eval_eq_root_distance_product_sq` の左辺は
 `fiberPolynomial A_H D_H c` の評価である。一方、Vélu の関数体表示を
 有限点 `R` の評価準同型へ通すと、分母が非零である限り

 `A_H(R.x) - c D_H(R.x) = (X_H(R)-c) D_H(R.x)`

 となる。本補題はこの橋だけを担当する。特殊枝の根積、分母の根積、
 二捩れ点の選択は仮定に押し込め、関数体の分数表示と正則評価の境界を
一つの教材定理として固定する。
-/
theorem veluHalf_base_eval_sub_eq_kernelXAt_sub_mul_denominator
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (R : Points E) (hR : R ∉ H) (c : AlgebraicClosure K) :
    (veluHalfNumeratorBase E H).eval R.xc -
        c * (veluHalfDenominatorBase E H).eval R.xc =
      (kernelXAt E H R hR - c) *
        (veluHalfDenominatorBase E H).eval R.xc := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let x := genericX E (AlgebraicClosure K)
  let d' : regularAlgebra E R :=
    ⟨Polynomial.aeval x (veluHalfDenominatorBase E H), by
      exact pointValuation_aeval_le_one E R
        (by intro h0; exact hR (h0 ▸ H.zero_mem)) _⟩
  let a' : regularAlgebra E R :=
    ⟨Polynomial.aeval x (veluHalfNumeratorBase E H), by
      exact pointValuation_aeval_le_one E R
        (by intro h0; exact hR (h0 ▸ H.zero_mem)) _⟩
  let x' : regularAlgebra E R :=
    ⟨veluX E H, veluX_regular_outside E H R hR⟩
  have hDgeneric :
      Polynomial.aeval x (veluHalfDenominatorBase E H) ≠ 0 := by
    exact veluHalfDenominatorBase_eval_genericX_ne_zero E H
  have hrel : veluX E H =
      Polynomial.aeval x (veluHalfNumeratorBase E H) /
        Polynomial.aeval x (veluHalfDenominatorBase E H) := by
    simpa only [x] using veluX_eq_veluHalfNumeratorBase_div_denominator E H ho
  have hcross : veluX E H *
        Polynomial.aeval x (veluHalfDenominatorBase E H) =
      Polynomial.aeval x (veluHalfNumeratorBase E H) := by
    rw [hrel]
    exact div_mul_cancel₀ _ hDgeneric
  have hsub : x' * d' = a' := by
    apply Subtype.ext
    exact hcross
  have hxeval : evalHom E R x' = kernelXAt E H R hR := by
    rw [evalHom_apply]
    exact value_eq E R (veluX E H) _ (kernelXAt E H R hR)
      (kernelAt_congr E H R hR).1
  have hdeval : evalHom E R d' =
      (veluHalfDenominatorBase E H).eval R.xc := by
    rw [evalHom_apply]
    exact value_aeval_eq_eval E R
      (by intro h0; exact hR (h0 ▸ H.zero_mem)) _
  have haevel : evalHom E R a' =
      (veluHalfNumeratorBase E H).eval R.xc := by
    rw [evalHom_apply]
    exact value_aeval_eq_eval E R
      (by intro h0; exact hR (h0 ▸ H.zero_mem)) _
  have hev := congrArg (evalHom E R) hsub
  have hmain :
      kernelXAt E H R hR * (veluHalfDenominatorBase E H).eval R.xc =
        (veluHalfNumeratorBase E H).eval R.xc := by
    simpa only [map_mul, hxeval, hdeval, haevel] using hev
  rw [← hmain]
  ring

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 二つの有限評価を一つの根差積へ接続する。

源の二捩れ代表 `P` における特殊ファイバーを、別の核外点 `R` で評価する。
前定理が左辺を `(X_H(R)-c) D_H(R.x)` へ戻し、分母評価の根積公式が
`D_H(R.x) = (∏(x(Q)-R.x))²` を供給する。その結果、半核移動根の距離積と
商座標の差が同じ等式に現れる。これは後続の `pair_relation` に渡す局所
交差評価であり、まだ三つの二捩れ根を掛け合わせる段階ではない。
-/
theorem veluHalf_base_special_fiber_intersection_eval
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K) (hPc : kernelXAt E H P hP = c)
    (R : Points E) (hR : R ∉ H) :
    (kernelXAt E H R hR - c) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - R.xc)) ^ 2 =
      (R.xc - P.xc) *
        (∏ Q : halfKernel E H,
          (R.xc - (P + Q.val.val).xc)) ^ 2 := by
  have hspecial := veluHalf_base_special_fiber_eval_eq_root_distance_product_sq
    E H ho P hP hneg c hPc R.xc
  have hvalue := veluHalf_base_eval_sub_eq_kernelXAt_sub_mul_denominator
    E H ho R hR c
  have hden := veluHalfDenominatorBase_eval_eq_root_product_sq E H R.xc
  have hfiber :
      (fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c).eval R.xc =
        (veluHalfNumeratorBase E H).eval R.xc -
          c * (veluHalfDenominatorBase E H).eval R.xc := by
    simp only [fiberPolynomial, eval_sub, eval_mul, eval_C]
  rw [hfiber, hvalue, hden] at hspecial
  simpa only [← Finset.prod_pow] using hspecial

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 標準対の二捩れ特殊ファイバーを半核因子へ同定する。

標準 `RatFunc` 対の次数条件と関数体表示から共通スカラー倍を取り出し、前二定理
で正規化ファイバーを半核対へ輸送する。その後、半核対について既に証明済みの
二捩れ特殊枝分解を使う。従って標準対側に互いに素性・モニック性・Wronskian
零点を重ねて仮定する必要はなく、無限遠点での次数正規化だけが残る。
-/
theorem veluX_standard_pair_special_fiber_of_odd_twoTorsion
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (hFdeg : F.natDegree = Nat.card H)
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    normalize (fiberPolynomial F G c) =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
        (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  obtain ⟨u, hu, hF, hG'⟩ :=
    veluX_standard_pair_proportional_to_veluHalf_base E H ho F G hG hrel hFdeg
  have htransport := normalize_fiberPolynomial_eq_of_proportional (c := c) hu hF hG'
  have hbase := veluHalf_base_special_fiber_of_odd_twoTorsion
    E H ho P hP hneg c hPc
  calc
    normalize (fiberPolynomial F G c) =
        normalize (fiberPolynomial (veluHalfNumeratorBase E H)
          (veluHalfDenominatorBase E H) c) := htransport
    _ = normalize (fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
          (fun Q : halfKernel E H => (P + Q.val.val).xc)) := by rw [hbase]
    _ = fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
          (fun Q : halfKernel E H => (P + Q.val.val).xc) :=
      (fiberFactor_monic _ _ _).normalize_eq_self

/-- [DkMath.Lib] 非自明な奇数核の特殊ファイバーは判別式零である。

前定理の半核因子分解を `fiberFactor_discr_eq_zero_of_nonempty` へ接続する。
`1 < Nat.card H` から `halfKernel_nonempty_of_one_lt_card` を得るため、
平方因子が実際に存在することを明示的に確認できる。従って自明核の場合を誤って
含めず、標準 `RatFunc` 対の正規化や判別式族の選択に依存しない特殊枝の判別式零性を
直接供給する。 -/
theorem veluHalf_base_special_fiber_discr_eq_zero_of_one_lt_card
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr = 0 := by
  have hfactor := veluHalf_base_special_fiber_of_odd_twoTorsion
    E H ho P hP hneg c hPc
  rw [hfactor]
  obtain ⟨Q, hQ⟩ := halfKernel_nonempty_of_one_lt_card E H ho hcard
  have huniv : (Finset.univ : Finset (halfKernel E H)).Nonempty :=
    ⟨⟨Q, hQ⟩, Finset.mem_univ _⟩
  exact fiberFactor_discr_eq_zero_of_nonempty
    (Finset.univ : Finset (halfKernel E H)) huniv P.xc
      (fun R : halfKernel E H => (P + R.val.val).xc)

/-- [DkMath.Lib] 二捩れ特殊枝の判別式零性を任意の代表へ輸送する。

`P` 自身が二捩れであることは要求せず、`2 • P ∈ H` だけを仮定する。奇数核では
倍写像の全単射性から同じ `kernelXAt` 値を持つ核外二捩れ代表 `T` を選べるため、
前定理を `T` へ適用して元の有限値 `c` の半核ファイバー判別式零性を得る。
これは特殊枝の幾何学的な「代表選択」と判別式計算を分離する教科書的な輸送定理である。
-/
theorem veluHalf_base_special_fiber_discr_eq_zero_of_two_smul_mem
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (P : Points E) (hP : P ∉ H) (hP2 : 2 • P ∈ H)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr = 0 := by
  obtain ⟨T, hT, hTneg, hTc⟩ :=
    exists_two_torsion_kernelXAt_representative_of_two_smul_mem
      E H ho P hP hP2 c hPc
  obtain ⟨hT', hTc'⟩ := hTc
  exact veluHalf_base_special_fiber_discr_eq_zero_of_one_lt_card
    E H ho hcard T hT' hTneg c hTc'

omit [CharZero K] [NeZero (2 : K)] in
/-- [DkMath.Lib] 半核対の一般枝ファイバーは全核軌道因子へ分解する。

`2 • P ∉ H` では軌道の x 座標が単射になる。半核分子・分母の次数公式から
`fiberPolynomial A_H D_H c` のモニック性と次数上界を供給し、平行移動不変性で
全軌道根を得た後、既存の単射根終端へ渡す。特殊枝の Wronskian はこの定理には
現れず、一般枝と特殊枝の代数的役割を明確に分離する。 -/
theorem veluHalf_base_general_fiber_of_two_smul_not_mem
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (htwo : 2 • P ∉ H)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c =
      ∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val).xc)) := by
  have hAmonic := veluHalfNumeratorBase_monic E H
  have hAdeg : (veluHalfNumeratorBase E H).natDegree = Nat.card H := by
    calc
      (veluHalfNumeratorBase E H).natDegree =
          1 + 2 * (halfKernel E H).card := veluHalfNumeratorBase_natDegree E H
      _ = 2 * (halfKernel E H).card + 1 := by omega
      _ = Nat.card H := card_halfKernel E H ho
  have hDdeg : (veluHalfDenominatorBase E H).natDegree =
      2 * (halfKernel E H).card := veluHalfDenominatorBase_natDegree E H
  have hDlt : (veluHalfDenominatorBase E H).natDegree <
      (veluHalfNumeratorBase E H).natDegree := by
    rw [hDdeg, hAdeg]
    have hc := card_halfKernel E H ho
    omega
  have hp : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).Monic := by
    unfold fiberPolynomial
    exact hAmonic.sub_of_left (degree_lt_degree
      ((natDegree_C_mul_le c (veluHalfDenominatorBase E H)).trans_lt hDlt))
  have hdeg : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).natDegree ≤ Nat.card H := by
    rw [fiberPolynomial_natDegree_eq_of_natDegree_lt hDlt, hAdeg]
  have hD : veluHalfDenominatorBase E H ≠ 0 :=
    (veluHalfDenominatorBase_monic E H).ne_zero
  have hrel := veluX_eq_veluHalfNumeratorBase_div_denominator E H ho
  have hroot : ∀ Q : H,
      (fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c).IsRoot ((P + Q.val).xc) := by
    intro Q
    have hQ : P + Q.val ∉ H := add_not_mem_kernel E H P hP Q
    exact fiberPolynomial_isRoot_of_veluX_eq_quotient E H
      (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H) hD hrel c
      (P + Q.val) hQ (by rw [kernelXAt_translation E H P hP Q, hPc])
  exact eq_fullKernel_factor_of_monic_of_injective_roots E H P htwo
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c) hp hroot hdeg

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 半核対の一般枝ファイバーは判別式非零である。

前定理の全核軌道因子分解と `orbit_x_injective_of_two_smul_not_mem` を
`separable_prod_X_sub_C_iff` へ渡す。次数正性は半核分子の次数公式から供給されるため、
判別式の非零性に標準係数対や正規化ファイバーを持ち込まない。 -/
theorem veluHalf_base_general_fiber_discr_ne_zero_of_two_smul_not_mem
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (htwo : 2 • P ∉ H)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr ≠ 0 := by
  rw [veluHalf_base_general_fiber_of_two_smul_not_mem E H ho P hP htwo c hPc]
  have hinj : Function.Injective (fun Q : H => ((P + Q.val).xc)) :=
    orbit_x_injective_of_two_smul_not_mem E H P htwo
  have hsep : (∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val).xc))).Separable := by
    exact separable_prod_X_sub_C_iff.mpr hinj
  have hdeg : 0 < (∏ Q : H,
      (Polynomial.X - Polynomial.C ((P + Q.val).xc))).degree := by
    rw [← natDegree_pos_iff_degree_pos,
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    simp only [Finset.card_univ]
    exact Fintype.card_pos_iff.mpr ⟨(0 : H)⟩
  exact discr_ne_zero_of_separable hdeg hsep

/-- [DkMath.Lib] 半核対の有限ファイバー判別式は二捩れ分岐を正確に検出する。

一般枝では前定理の分離性から判別式が非零、特殊枝では半核の平方因子から判別式が
零になる。`1 < Nat.card H` は特殊枝で半核を一つ選ぶためだけに必要であり、
この同値は標準 `RatFunc` 対の存在や判別式族の構成に依存しない。 -/
theorem veluHalf_base_fiber_discr_eq_zero_iff_two_smul_mem
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (P : Points E) (hP : P ∉ H)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr = 0 ↔ 2 • P ∈ H := by
  constructor
  · intro hzero
    by_contra hnot
    exact (veluHalf_base_general_fiber_discr_ne_zero_of_two_smul_not_mem
      E H ho P hP hnot c hPc) hzero
  · intro htwo
    exact veluHalf_base_special_fiber_discr_eq_zero_of_two_smul_mem
      E H ho hcard P hP htwo c hPc

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

