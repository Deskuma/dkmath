/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.Algebra.RationalPolynomialDiscriminant
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBifurcation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantFamily"

/-!
# Vélu 判別式族と有限核の二捩れ分岐

`fiberDiscriminantFamily F G` は、固定係数対 `F,G` に対して全有限ファイバーを
一つの多項式で記述する。前モジュールの有限ファイバー分岐定理は
`fiberPolynomial F G c` の判別式を直接扱うため、本モジュールでは
`fiberDiscriminantFamily_eval_of_natDegree_lt` を適用して両者を接続する。

この接続で新たな楕円曲線の計算は行わない。無限遠点で一度選ばれた係数対を
そのまま使い、既存の全代表版の幾何学的分岐判定を判別式族の評価へ輸送する。
したがって、ここで得られるのは「各ファイバーを個別に調べる」記述から
「一つの多項式の零点を調べる」記述への厳密な API である。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.Algebra.RationalPolynomialDiscriminant
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantFamily
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]

/-- [DkMath.Lib] 判別式族の評価を、固定係数対の幾何学的分岐へ輸送する。

`exists_veluX_fixed_pair_discriminant_branch_iff_all_points` が供給する同一の
`F,G` に対し、`fiberDiscriminantFamily_eval_of_natDegree_lt` を適用する。
これにより任意の核外代表 `P` について、`kernelXAt P = c` のファイバーが
二捩れ枝であることと、判別式族を `c` で評価した値が零であることが同値になる。
-/
theorem exists_veluX_fixed_pair_discriminant_family_branch_iff_all_points
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    ∃ F G : (AlgebraicClosure K)[X],
      IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
        G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        ∀ (c : AlgebraicClosure K) (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c →
            ((fiberDiscriminantFamily F G).eval c = 0 ↔ 2 • P ∈ H) := by
  obtain ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, hbranch⟩ :=
    exists_veluX_fixed_pair_discriminant_branch_iff_all_points E H ho hcard
  refine ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, ?_⟩
  intro c P hP hPc
  rw [fiberDiscriminantFamily_eval_of_natDegree_lt F G hGlt c]
  exact hbranch c P hP hPc

/-- [DkMath.Lib] 判別式族の零点を二捩れ有限ファイバーの像として分類する。

各 `c` には `exists_kernelXAt_eq` により核外代表があるため、前定理の代表付き
同値から代表を量化消去できる。結論は、判別式族の零点集合が
`kernelXAt` による二捩れ枝の値の像に一致することを命題として表したものである。
この段階では剰余群や局所付値を仮定せず、有限ファイバーの幾何学だけを固定する。
-/
theorem exists_veluX_fixed_pair_discriminant_family_zero_iff_two_torsion_image
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    ∃ F G : (AlgebraicClosure K)[X],
      IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
        G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        ∀ c : AlgebraicClosure K,
          (fiberDiscriminantFamily F G).eval c = 0 ↔
            ∃ P : Points E, ∃ hP : P ∉ H,
              kernelXAt E H P hP = c ∧ 2 • P ∈ H := by
  obtain ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, hbranch⟩ :=
    exists_veluX_fixed_pair_discriminant_family_branch_iff_all_points E H ho hcard
  refine ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, ?_⟩
  intro c
  constructor
  · intro hzero
    obtain ⟨P, hP, hPc⟩ := exists_kernelXAt_eq E H c
    have htwo : 2 • P ∈ H := by
      exact (hbranch c P hP hPc).mp hzero
    exact ⟨P, hP, hPc, htwo⟩
  · rintro ⟨P, hP, hPc, htwo⟩
    have hdisc := (hbranch c P hP hPc).mpr htwo
    exact hdisc

/-- [DkMath.Lib] 明示的半核対の判別式族は二捩れ分岐を検出する。

`A_H = veluHalfNumeratorBase E H` と `D_H = veluHalfDenominatorBase E H` は
次数公式から `deg D_H < deg A_H` を満たす。したがって既存の判別式族評価定理を
そのまま特殊化でき、有限値 `c = kernelXAt(P)` における族の零性は、既に確立した
半核ファイバー判別式の同値
`discr (A_H - c D_H) = 0 ↔ 2 • P ∈ H` と一致する。標準 `RatFunc` 対の選択や
スカラー倍判別式公式を経由しない、明示係数による直接経路である。
-/
theorem veluHalf_base_discriminantFamily_eval_eq_zero_iff_two_smul_mem
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (P : Points E) (hP : P ∉ H)
    (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    (fiberDiscriminantFamily (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).eval c = 0 ↔ 2 • P ∈ H := by
  have hdeg : (veluHalfDenominatorBase E H).natDegree <
      (veluHalfNumeratorBase E H).natDegree := by
    rw [veluHalfDenominatorBase_natDegree, veluHalfNumeratorBase_natDegree]
    have hc := card_halfKernel E H ho
    omega
  rw [fiberDiscriminantFamily_eval_of_natDegree_lt
    (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H) hdeg c]
  exact veluHalf_base_fiber_discr_eq_zero_iff_two_smul_mem
    E H ho hcard P hP c hPc

/-- [DkMath.Lib] 明示的半核判別式族の零点を二捩れ枝の値像へ分類する。

`exists_kernelXAt_eq` によって任意の有限値 `c` は核外点で実現されるため、前定理の
代表付き同値から点を量化消去できる。従って明示的な族の零点集合は、`kernelXAt` が
二捩れ枝 `2 • P ∈ H` 上で取る値の像と厳密に一致する。これは標準係数対の存在定理
を使わず、半核係数対そのものを判別式族として公開する API である。
-/
theorem veluHalf_base_discriminantFamily_eval_eq_zero_iff_two_torsion_image
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (c : AlgebraicClosure K) :
    (fiberDiscriminantFamily (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).eval c = 0 ↔
      ∃ P : Points E, ∃ hP : P ∉ H,
        kernelXAt E H P hP = c ∧ 2 • P ∈ H := by
  constructor
  · intro hzero
    obtain ⟨P, hP, hPc⟩ := exists_kernelXAt_eq E H c
    exact ⟨P, hP, hPc,
      (veluHalf_base_discriminantFamily_eval_eq_zero_iff_two_smul_mem
        E H ho hcard P hP c hPc).mp hzero⟩
  · rintro ⟨P, hP, hPc, htwo⟩
    exact (veluHalf_base_discriminantFamily_eval_eq_zero_iff_two_smul_mem
      E H ho hcard P hP c hPc).mpr htwo

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
