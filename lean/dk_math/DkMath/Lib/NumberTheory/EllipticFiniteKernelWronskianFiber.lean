/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianFiber"

/-!
# Wronskian 零点から特殊ファイバー因子への終端接続

このモジュールは、有限点で証明された Vélu Wronskian 零点を、既存の
`RootProduct` 側のファイバー因子同定定理へ渡す終端層である。

数学的な流れは次の通りである。

* `veluX_standard_pair_wronskian_root_of_odd_twoTorsion` が、標準分子分母対の
  Wronskian 零点を各半核移動点で供給する。
* `exists_veluX_normalized_fiberFactor_of_wronskian_transport` が、その零点を
  `fiberPolynomial` の二重根情報へ変換する。
* 最後に、正規化されたファイバー多項式を `fiberFactor` と同定する。

ここで標数零を仮定しているのは、既存の `RootProduct` の終端 API に合わせる
ためであり、Wronskian 特殊化そのものの標数条件を強めるためではない。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.Algebra
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianFiber
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]

/-- [DkMath.Lib] 奇数核の二捩れ枝で、Wronskian 仮定なしに正規化ファイバーを同定する。

`RootProduct` の一般終端定理が要求する
`∀ Q : halfKernel E H, W(F,G)(x(P+Q)) = 0` を、各標準対 `(F,G)` に対して
有限点 Wronskian 定理から構成する。分母評価の非零性は、`genericX` の超越性と
`G ≠ 0` から直接得られる。したがって、この定理の入力には幾何学的
Wronskian 仮定を残していない。

出力は、既存の `fiberFactor` が表す「基点の単純根と半核移動点の二重根」の
正規化ファイバー因子分解である。 -/
theorem exists_veluX_normalized_fiberFactor_of_odd_twoTorsion
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    ∃ F G : (AlgebraicClosure K)[X],
      IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
        G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        fiberPolynomial F G c ≠ 0 ∧
        (normalize (fiberPolynomial F G c)).Monic ∧
        (normalize (fiberPolynomial F G c)).natDegree = Nat.card H ∧
        (∀ (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c →
            (normalize (fiberPolynomial F G c)).IsRoot P.xc) ∧
        normalize (fiberPolynomial F G c) =
          fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
            (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  apply exists_veluX_normalized_fiberFactor_of_wronskian_transport E H ho P hP hneg c hPc
  intro F G hcop hG hrel Q
  have hGaeval : aeval (genericX E (AlgebraicClosure K)) G ≠ 0 := by
    intro hzero
    exact hG ((transcendental_iff.mp
      (genericX_transcendental_for_wronskian E)) G hzero)
  have hQ : Q.val ≠ 0 := ((mem_halfKernel E H Q.val).mp Q.property).1
  exact veluX_standard_pair_wronskian_root_of_odd_twoTorsion
    E H ho F G hGaeval hrel P hP hneg Q.val hQ

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
