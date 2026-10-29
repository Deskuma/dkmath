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

/-- 固定した係数対に対する二分岐の結論部分。

`F,G` 自体はこの命題の外で一度だけ選択する。ここではファイバー値 `c` と
核外点 `P` ごとに、同じ `F,G` が一般型または特殊型のどちらを取るかだけを
記録する。
-/
def fixedPairFiberBranch
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (F G : (AlgebraicClosure K)[X]) (c : AlgebraicClosure K) (P : Points E)
    (_hP : P ∉ H) : Prop :=
    (2 • P ∉ H ∧
      normalize (fiberPolynomial F G c) =
        ∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val).xc))) ∨
    (2 • P ∈ H ∧
      ∃ T : Points E, T ∉ H ∧ -T = T ∧
        ∃ hT : T ∉ H, kernelXAt E H T hT = c ∧
          normalize (fiberPolynomial F G c) =
            fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
              (fun Q : halfKernel E H => (T + Q.val.val).xc))

omit [CharZero K] in
/-- [DkMath.Lib] 固定対の有限ファイバーは先頭係数を変えない。

`deg G < deg F` なら `cG` は `F` より低次数なので、`F - cG` の最高次項は
常に `F` から来る。従って正規化係数はファイバー値 `c` に依存しない。この
一変数の次数比較は、全ファイバーを二変数族 `F(X) - C G(X)` として扱う際の
基礎補題である。
-/
theorem fiberPolynomial_leadingCoeff_eq_of_natDegree_lt
    {F G : (AlgebraicClosure K)[X]} {c : AlgebraicClosure K}
    (hdeg : G.natDegree < F.natDegree) :
    (fiberPolynomial F G c).leadingCoeff = F.leadingCoeff := by
  have hF : F ≠ 0 := by
    intro hzero
    subst F
    exact (Nat.not_lt_zero _ hdeg)
  rw [fiberPolynomial, leadingCoeff_sub_of_degree_lt]
  calc
    degree (Polynomial.C c * G) ≤ (natDegree (Polynomial.C c * G) : WithBot ℕ) :=
      degree_le_natDegree
    _ < (F.natDegree : WithBot ℕ) := by
      exact_mod_cast (natDegree_C_mul_le c G).trans_lt hdeg
    _ = degree F := (degree_eq_natDegree hF).symm

/-- [DkMath.Lib] 任意の固定標準係数対で、核外ファイバーの二分岐を閉じる。

`hFdeg`、`hGlt`、`hrel` は `F,G` が無限遠点で一度選ばれた標準対であることを
表す。`fiberPolynomial` の非零性、正規化モニック性、次数はこの次数条件から
内部で構成する。一般枝では根積と次数比較、特殊枝では二捩れ代表と
`normalize_fiberPolynomial_eq_orbit_x_fiberFactor_of_veluX_quotient_of_wronskian_roots`
を使う。
-/
theorem fixedPairFiberBranch_of_veluX_quotient
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hcop : IsCoprime F G) (hG : G ≠ 0)
    (hFdeg : F.natDegree = Nat.card H) (hGlt : G.natDegree < F.natDegree)
    (hrel : veluX E H =
      aeval (genericX E (AlgebraicClosure K)) F /
        aeval (genericX E (AlgebraicClosure K)) G)
    (c : AlgebraicClosure K) (P : Points E) (hP : P ∉ H)
    (hPc : kernelXAt E H P hP = c) :
    fixedPairFiberBranch E H F G c P hP := by
  have hGaeval : aeval (genericX E (AlgebraicClosure K)) G ≠ 0 := by
    intro hzero
    exact hG ((transcendental_iff.mp
      (genericX_transcendental_for_wronskian E)) G hzero)
  have hp0 : fiberPolynomial F G c ≠ 0 := by
    intro hp
    have hid : aeval (genericX E (AlgebraicClosure K))
        (fiberPolynomial F G c) =
        (veluX E H - algebraMap (AlgebraicClosure K)
          (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) *
          aeval (genericX E (AlgebraicClosure K)) G := by
      rw [fiberPolynomial, map_sub, map_mul, aeval_C, hrel]
      field_simp [hGaeval]
    have hv : aeval (genericX E (AlgebraicClosure K))
        (fiberPolynomial F G c) ≠ 0 := by
      rw [hid]
      exact mul_ne_zero (sub_ne_zero.mpr (veluX_ne_const E H c)) hGaeval
    exact hv (by rw [hp, map_zero])
  have hnorm : (normalize (fiberPolynomial F G c)).Monic :=
    Polynomial.monic_normalize hp0
  have hdeg : (fiberPolynomial F G c).natDegree = Nat.card H := by
    rw [fiberPolynomial_natDegree_eq_of_natDegree_lt hGlt, hFdeg]
  by_cases htwo : 2 • P ∈ H
  · obtain ⟨T, hT, hTneg, hTc⟩ :=
      exists_two_torsion_kernelXAt_representative_of_two_smul_mem
        E H ho P hP htwo c hPc
    obtain ⟨hT', hTc'⟩ := hTc
    have hwronskian : ∀ Q : halfKernel E H,
        (wronskian F G).IsRoot ((T + Q.val.val).xc) := by
      intro Q
      have hQ : Q.val ≠ 0 := ((mem_halfKernel E H Q.val).mp Q.property).1
      exact veluX_standard_pair_wronskian_root_of_odd_twoTorsion
        E H ho F G hGaeval hrel T hT' hTneg Q.val hQ
    have hfactor :=
      normalize_fiberPolynomial_eq_orbit_x_fiberFactor_of_veluX_quotient_of_wronskian_roots
        E H ho T hT' hTneg F G hcop hG hrel c hp0 hTc'
        hwronskian hdeg.le
    exact Or.inr ⟨htwo, T, hT, hTneg, hT', hTc', hfactor⟩
  · have hroot : ∀ Q : H,
        (normalize (fiberPolynomial F G c)).IsRoot ((P + Q.val).xc) := by
      intro Q
      have hQ : P + Q.val ∉ H := add_not_mem_kernel E H P hP Q
      have hroot' := fiberPolynomial_isRoot_of_veluX_eq_quotient E H F G hG hrel c
        (P + Q.val) hQ (by rw [kernelXAt_translation E H P hP Q, hPc])
      rw [← mem_roots hp0] at hroot'
      apply (mem_roots hnorm.ne_zero).mp
      rw [Polynomial.roots_normalize]
      exact hroot'
    have hdeg_norm : (normalize (fiberPolynomial F G c)).natDegree ≤ Nat.card H := by
      rw [Polynomial.natDegree_normalize]
      exact hdeg.le
    have hfactor := eq_fullKernel_factor_of_monic_of_injective_roots E H P htwo
      (normalize (fiberPolynomial F G c)) hnorm hroot hdeg_norm
    exact Or.inl ⟨htwo, hfactor⟩

/-- [DkMath.Lib] 無限遠点で一度選んだ `(F,G)` を全ファイバーへ固定する。

`exists_veluX_rational_at_infinity` から `F = r.num`, `G = r.denom` を一度だけ
選ぶ。以後、任意の `c` と任意の核外点 `P` satisfying `kernelXAt P = c` に対し、
同じ係数対を `fixedPairFiberBranch_of_veluX_quotient` へ渡せる。
-/
theorem exists_veluX_fixed_pair_factorization
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    ∃ F G : (AlgebraicClosure K)[X],
      IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
        G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        ∀ (c : AlgebraicClosure K) (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c → fixedPairFiberBranch E H F G c P hP := by
  obtain ⟨r, hgap, hnum, hrel⟩ := exists_veluX_rational_at_infinity E H
  refine ⟨r.num, r.denom, r.isCoprime_num_denom, r.denom_ne_zero, hnum, ?_, hrel, ?_⟩
  · omega
  · intro c P hP hPc
    exact fixedPairFiberBranch_of_veluX_quotient E H ho r.num r.denom
      r.isCoprime_num_denom r.denom_ne_zero hnum (by omega) hrel c P hP hPc

/-- [DkMath.Lib] 固定した標準係数対を全有限ファイバーへ実際に供給する。

前定理は、与えられた核外点 `P` がファイバー値 `c` を実現しているときの
分岐を返す。この定理では既存の `exists_kernelXAt_eq` を組み合わせ、任意の
`c` に対してそのような `P` と核外証明を一つ選ぶ。従って `F,G` の選択は
無限遠点で一度だけ行われ、有限ファイバーごとに係数を取り直す必要がない。
この API は存在量化されたファイバー代表を明示するため、点評価の正則性や
標数零の次数条件を隠さずに後続の商構成へ渡せる。
-/
theorem exists_veluX_fixed_pair_factorization_all_fibers
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    ∃ F G : (AlgebraicClosure K)[X],
      IsCoprime F G ∧ G ≠ 0 ∧ F.natDegree = Nat.card H ∧
        G.natDegree < F.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure K)) F /
          aeval (genericX E (AlgebraicClosure K)) G ∧
        ∀ c : AlgebraicClosure K, ∃ (P : Points E) (hP : P ∉ H),
          kernelXAt E H P hP = c ∧ fixedPairFiberBranch E H F G c P hP := by
  obtain ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, hbranch⟩ :=
    exists_veluX_fixed_pair_factorization E H ho
  refine ⟨F, G, hcop, hG, hFdeg, hGlt, hrel, ?_⟩
  intro c
  obtain ⟨P, hP, hPc⟩ := exists_kernelXAt_eq E H c
  exact ⟨P, hP, hPc, hbranch c P hP hPc⟩

/-- [DkMath.Lib] 固定係数対の二捩れ特殊枝では有限ファイバーの判別式が零になる。

特殊枝の因子分解は、正規化ファイバーを一本の単純因子と半核因子の二乗積へ
同定する。非自明な奇数核なら `halfKernel_nonempty_of_one_lt_card` で二乗因子を
一つ選べるため、`discr_eq_zero_of_sq_dvd_normalize` が正規化を取り除き、実際の
`fiberPolynomial F G c` の判別式零性を返す。一般枝はこの定理の対象外であり、
根の分離からの非零性は別の補題として保持する。 -/
theorem fixedPairFiberBranch_discr_eq_zero_of_two_smul_mem
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (F G : (AlgebraicClosure K)[X])
    (hFdeg : F.natDegree = Nat.card H) (hGlt : G.natDegree < F.natDegree)
    (c : AlgebraicClosure K) (P : Points E) (hP : P ∉ H)
    (hbranch : fixedPairFiberBranch E H F G c P hP)
    (htwo : 2 • P ∈ H) :
    (fiberPolynomial F G c).discr = 0 := by
  rcases hbranch with hgeneral | hspecial
  · exact (hgeneral.1 htwo).elim
  · rcases hspecial with ⟨_, T, hT, hTneg, hT', hTc, hfactor⟩
    obtain ⟨Q, hQ⟩ := halfKernel_nonempty_of_one_lt_card E H ho hcard
    let Q' : halfKernel E H := ⟨Q, hQ⟩
    have hdiv_factor :
        (Polynomial.X - Polynomial.C ((T + Q'.val.val).xc)) ^ 2 ∣
          fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
            (fun Q : halfKernel E H => (T + Q.val.val).xc) := by
      unfold fiberFactor
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ Q')) _
    have hdiv_norm :
        (Polynomial.X - Polynomial.C ((T + Q'.val.val).xc)) ^ 2 ∣
          normalize (fiberPolynomial F G c) := by
      rw [hfactor]
      exact hdiv_factor
    have hdeg : 0 < (fiberPolynomial F G c).degree := by
      rw [← natDegree_pos_iff_degree_pos,
        fiberPolynomial_natDegree_eq_of_natDegree_lt hGlt, hFdeg]
      omega
    exact discr_eq_zero_of_sq_dvd_normalize hdeg hdiv_norm
      (not_isUnit_of_degree_pos _ (by simp))

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
