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
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantInput
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]

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
