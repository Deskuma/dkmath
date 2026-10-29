/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBase

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantInput"

/-!
# 判別式積公式へ渡す半核分母の入力

Anthropic 版の `delta_identity` では、半核多項式 `hP` を三つの二捩れ根で
評価し、根距離積 `H₁,H₂,H₃` と接線因子積 `U` を結び付ける。このモジュールは
そのうち係数計算に依存しない部分を DkMath の明示的な
`veluHalfDenominatorBase` へ移す。

分母は各 `Q` に対して同じ因子を二度持つので、根 `e` で評価すると
`(∏ (e - x(Q)))²` になる。源曲線の二捩れ三根に対する接線平方公式と組み合わせると、
判別式積へ渡す根距離入力が得られる。商モデルの三根差関係そのものは、この層では
仮定せず、後続の `pair_relation` 消費者へ残す。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.NumberTheory.WeierstrassVeluPair
open DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open DkMath.Lib.Algebra.RationalPolynomialFiber
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantInput
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- [DkMath.Lib] 各 Vélu 補正分母はモニック二次式である。 -/
theorem xCorrectionDenominator_monic (a : AlgebraicClosure K) :
    (xCorrectionDenominator a).Monic := by
  unfold xCorrectionDenominator
  exact (monic_X_sub_C a).mul (monic_X_sub_C a)

omit [CharZero K] in
/-- [DkMath.Lib] 各 Vélu 補正分母の次数は二である。 -/
theorem xCorrectionDenominator_natDegree (a : AlgebraicClosure K) :
    (xCorrectionDenominator a).natDegree = 2 := by
  change ((X - C a) * (X - C a)).natDegree = 2
  rw [natDegree_mul (monic_X_sub_C a).ne_zero (monic_X_sub_C a).ne_zero]
  simp

omit [CharZero K] in
/-- [DkMath.Lib] 各 Vélu 補正分子の次数は高々一である。

`xCorrectionNumerator = C(t) (X - C(a)) + C(u)` なので、補正分子は
線型項と定数項の和に過ぎない。この局所次数境界が、半核共通分子の
補正和を主項 `X * D` より低次数に置くための入力になる。
-/
theorem xCorrectionNumerator_natDegree_le_one
    (W : WeierstrassCurve (AlgebraicClosure K)) (a b : AlgebraicClosure K) :
    (xCorrectionNumerator W a b).natDegree ≤ 1 := by
  unfold xCorrectionNumerator
  calc
    (C (momentT W a) * (X - C a) + C ((2 * b + W.a₁ * a + W.a₃) ^ 2)).natDegree ≤
        max (C (momentT W a) * (X - C a)).natDegree
          (C ((2 * b + W.a₁ * a + W.a₃) ^ 2)).natDegree :=
      natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
      · rw [natDegree_C]
        omega

omit [CharZero K] in
/-- [DkMath.Lib] 主項より低次数の有限補正和を加えてもモニック性は保たれる。

`commonNumerator = X * commonDenominator + Σ Nᵢ Eᵢ` の形で、各補正項の
次数が主項より真に小さければ、最高次係数は主項の一だけである。この一般補題は
半核の具体的な次数計算をここへ埋め込まず、後続の特殊化が供給すべき条件を
明示する。
-/
theorem commonNumerator_monic_of_term_degree_lt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (N D : ι → (AlgebraicClosure K)[X])
    (hD : (commonDenominator s D).Monic)
    (hterm : ∀ i ∈ s,
      (N i * erasedProduct s D i).degree <
        (X * commonDenominator s D).degree) :
    (commonNumerator s N D).Monic := by
  unfold commonNumerator
  apply (monic_X.mul hD).add_of_left
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
  · exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr ((monic_X.mul hD).ne_zero))
  · intro i hi
    exact hterm i hi

omit [CharZero K] in
/-- [DkMath.Lib] 二次モニック因子の除去積の次数を数える。

各 `D i` がモニック二次式なら、`erasedProduct s D i` の次数は
`2 * (s.erase i).card` になる。半核補正項の次数を、全分母の主項と
比較する際に使う有限積の数え上げ補題である。
-/
theorem erasedProduct_natDegree_eq_two_mul_card
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → (AlgebraicClosure K)[X])
    (hmonic : ∀ i ∈ s, (D i).Monic)
    (hdeg : ∀ i ∈ s, (D i).natDegree = 2)
    {i : ι} (_hi : i ∈ s) :
    (erasedProduct s D i).natDegree = 2 * (s.erase i).card := by
  unfold erasedProduct
  rw [natDegree_prod_of_monic]
  · have hsum :
        (∑ j ∈ s.erase i, (D j).natDegree) =
          ∑ _j ∈ s.erase i, 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hdeg j (Finset.mem_of_mem_erase hj)
    rw [hsum]
    simp [Nat.mul_comm]
  · intro j hj
    exact hmonic j (Finset.mem_of_mem_erase hj)

omit [CharZero K] in
/-- [DkMath.Lib] 半核共通分母はモニックである。 -/
theorem veluHalfDenominatorBase_monic
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    (veluHalfDenominatorBase E H).Monic := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  apply monic_prod_of_monic
  intro Q hQ
  exact xCorrectionDenominator_monic Q.val.xc

omit [CharZero K] in
/-- [DkMath.Lib] 半核共通分母の次数は半核の濃度の二倍である。 -/
theorem veluHalfDenominatorBase_natDegree
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    (veluHalfDenominatorBase E H).natDegree = 2 * (halfKernel E H).card := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  rw [natDegree_prod_of_monic]
  · simp only [xCorrectionDenominator_natDegree,
      Finset.sum_const, nsmul_eq_mul]
    simp [Nat.mul_comm]
  · intro Q hQ
    exact xCorrectionDenominator_monic Q.val.xc

/-! ## 標準分子への最小正規化入力 -/

omit [CharZero K] in
/-- [DkMath.Lib] 交差乗算と互いに素性から標準分子の可除性を得る。

`F * D = A * G` は、評価写像の分数表示を多項式の恒等式へ戻したもの
である。`IsCoprime F G` を使えば、ここから直ちに `F ∣ A` が従う。
この補題は分子と共通分母が同じ多項式だと主張しない。後者には次数・
モニック性の比較が別途必要であるため、正規化の最初の安全な段階として
可除性だけを公開する。
-/
theorem dvd_of_cross_relation_of_coprime
    {F G A D : (AlgebraicClosure K)[X]}
    (hcop : IsCoprime F G) (hcross : F * D = A * G) : F ∣ A := by
  apply hcop.dvd_of_dvd_mul_right
  rw [← hcross]
  exact dvd_mul_right F D

omit [CharZero K] in
/-- [DkMath.Lib] 半核分母を源の根距離積へ評価する。

`veluHalfDenominatorBase` の各因子は
`(X - C x(Q)) (X - C x(Q))` であるため、評価点 `e` では
`(∏ (e - x(Q)))²` が現れる。これは Anthropic 版の `hP²` に対応する。
-/
theorem veluHalfDenominatorBase_eval_eq_root_distance_product_sq
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (e : AlgebraicClosure K) :
    (veluHalfDenominatorBase E H).eval e =
      ∏ Q ∈ halfKernel E H, (e - Q.val.xc) ^ 2 := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  simp only [eval_prod, xCorrectionDenominator, eval_mul, eval_sub, eval_X, eval_C]
  simp [pow_two, Finset.prod_mul_distrib]

omit [CharZero K] in
/-- [DkMath.Lib] 分母評価を反転した根距離積の二乗へ移す。

各距離の向きを反転しても二乗が外側にあるため全体の符号は消える。
ここで `x(Q) - e` の向きを固定しておくと、源曲線の二捩れ根積と
`pair_relation` を後から接続しやすい。
-/
theorem veluHalfDenominatorBase_eval_eq_root_product_sq
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (e : AlgebraicClosure K) :
    (veluHalfDenominatorBase E H).eval e =
      ∏ Q ∈ halfKernel E H, (Q.val.xc - e) ^ 2 := by
  rw [veluHalfDenominatorBase_eval_eq_root_distance_product_sq]
  apply Finset.prod_congr rfl
  intro Q hQ
  ring

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
