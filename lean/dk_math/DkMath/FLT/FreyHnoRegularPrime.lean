/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStableLine
import DkMath.FLT.Kummer.RegularPrimeFLT

#print "file: DkMath.FLT.FreyHnoRegularPrime"

/-!
# 正則素数では既存 GN–Kummer FLT が Source を排除する

既存 `not_int_solution_regular_prime` は、正則性を類群濃度との互いに素性として
受け取り、非零・原始整数解を排除する。`Source` はその全算術入力を保持している。
従って正則素数に対する hno は、残余表現を再研究せずに得られる。

逆に `Source p` が与えられたなら、`p` は `p` 次円分体の類群濃度を割る。
この必要条件は「非正則素数でも Source が存在する」とは言わない。
また本章の論理の向きは **完成済み GN–Kummer FLT → hno** である。
GN–Kummer FLT 自身を証明するために本章を使ってはならない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.RepresentationTheory
open scoped NumberField

variable {p : ℕ} [Fact p.Prime] (S : Source p)

include S in
/-- 正則性は任意の適切な円分体で明示する。原始性は同じ Source から供給する。 -/
theorem false_of_regular_prime
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) : False :=
  Kummer.not_int_solution_regular_prime hζ hp5 hreg
    S.a_ne S.b_ne S.c_ne S.coprime S.equation

/-- 正則素数での hno。正則性を消した一般 hno とは区別する。 -/
theorem residual_hno_of_regular_prime
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L :=
  (S.false_of_regular_prime hζ hp5 hreg).elim

include S in
/-- 残存 Source の指数は、標準 `p` 次円分体の類群濃度を割る。
これは GN–Kummer の既存 FLT による必要条件であり、新たな類数計算ではない。 -/
theorem prime_dvd_cyclotomic_classGroup_card (hp5 : 5 ≤ p) :
    p ∣ Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) := by
  by_contra hn
  exact S.false_of_regular_prime
    (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)) hp5
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn)

end DkMath.FLT.Frey.Source
