/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianFiber

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBifurcation"

/-!
# 奇数核ファイバーの二分岐 API

一般枝では `2 • P ∉ H` により全核軌道の x 座標が相異なり、正規化ファイバーは
一次因子積になる。例外枝では、奇数核の倍写像逆元から同じファイバー値を持つ
二捩れ代表 `T` を選び、前モジュールの Wronskian 証明を通じて半核因子の二重根を
得る。

この定理は二つの既存終端を一つの `Or` にまとめるだけであり、一般枝の根積理論や
特殊枝の Wr​onskian 微分計算を再証明しない。従って、後続の判別式・還元理論は
`2 • P ∉ H` の場合分けを一箇所で消化できる。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianBifurcation
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]

/-- [DkMath.Lib] 核外ファイバーを一般枝と二捩れ特殊枝へ完全に分岐する。

入力 `hPc` は、点 `P` が核外で `kernelXAt P = c` を満たすことだけを表す。
`2 • P ∉ H` の枝では既存の全核軌道因子分解を返す。
`2 • P ∈ H` の枝では、既存の代表選択
`exists_two_torsion_kernelXAt_representative_of_two_smul_mem` により、同じ
ファイバー値 `c` を持つ二捩れ代表 `T` を選び、Wronskian 特殊化済みの
`exists_veluX_normalized_fiberFactor_of_odd_twoTorsion` を適用する。

従って結論は、一般枝の相異なる一次根積か、特殊枝の単純根と半核二重根積かの
いずれかである。 -/
theorem exists_veluX_normalized_fiberFactor_or_fullKernel
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (c : AlgebraicClosure K) (P : Points E)
    (hPc : ∃ hP : P ∉ H, kernelXAt E H P hP = c) :
    (2 • P ∉ H ∧
      ∃ F G : (AlgebraicClosure K)[X],
        IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
          G.natDegree < F.natDegree ∧
          veluX E H =
            aeval (genericX E (AlgebraicClosure K)) F /
              aeval (genericX E (AlgebraicClosure K)) G ∧
          fiberPolynomial F G c ≠ 0 ∧
          (normalize (fiberPolynomial F G c)).Monic ∧
          (normalize (fiberPolynomial F G c)).natDegree = Nat.card H ∧
          normalize (fiberPolynomial F G c) =
            ∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val).xc))) ∨
    (2 • P ∈ H ∧
      ∃ T : Points E, T ∉ H ∧ -T = T ∧
        ∃ hT : T ∉ H, kernelXAt E H T hT = c ∧
          ∃ F G : (AlgebraicClosure K)[X],
            IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
              G.natDegree < F.natDegree ∧
              veluX E H =
                aeval (genericX E (AlgebraicClosure K)) F /
                  aeval (genericX E (AlgebraicClosure K)) G ∧
              fiberPolynomial F G c ≠ 0 ∧
              (normalize (fiberPolynomial F G c)).Monic ∧
              (normalize (fiberPolynomial F G c)).natDegree = Nat.card H ∧
              (∀ (R : Points E) (hR : R ∉ H),
                kernelXAt E H R hR = c →
                  (normalize (fiberPolynomial F G c)).IsRoot R.xc) ∧
              normalize (fiberPolynomial F G c) =
                fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
                  (fun Q : halfKernel E H => (T + Q.val.val).xc)) := by
  obtain ⟨hP, hPc⟩ := hPc
  by_cases htwo : 2 • P ∈ H
  · obtain ⟨T, hT, hTneg, hTc⟩ :=
      exists_two_torsion_kernelXAt_representative_of_two_smul_mem
        E H ho P hP htwo c hPc
    obtain ⟨hT', hTc'⟩ := hTc
    have hfactor := exists_veluX_normalized_fiberFactor_of_odd_twoTorsion
      E H ho T hT hTneg c hTc'
    exact Or.inr ⟨htwo, T, hT, hTneg, hT', hTc', hfactor⟩
  · have hfactor := exists_veluX_normalized_fullKernel_factor_of_two_smul_not_mem
      E H c P htwo ⟨hP, hPc⟩
    exact Or.inl ⟨htwo, hfactor⟩

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
