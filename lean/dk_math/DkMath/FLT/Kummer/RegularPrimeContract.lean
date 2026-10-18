/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNCaseIContract
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import Mathlib.NumberTheory.FLT.Basic

#print "file: DkMath.FLT.Kummer.RegularPrimeContract"

/-!
# 固定した位相契約だけを使う FLT 終端

Case I は `SolutionPacketProvider` が作る Packet を、固定した係数障害へ渡す。
Case II は `RegularDescent.Conditions` を受け取り、実装済みの正深度 State 降下を使う。
共役単元の具体的な証明や、類群・単元 criterion の供給方法には依存しない。

これは仮定を隠す入口ではない。呼出側は両契約の証明を実際に供給する必要がある。
既定の正則素数実装は `RegularPrimeFLT` がそれらを証明して渡す。
整数版は `a,b,c ≠ 0` を前提とし、符号と共通因子には制限を課さない。
-/

namespace DkMath.FLT.Kummer

open DkMath.Lib.NumberTheory
open scoped NumberField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- 原始的な非零整数反例を二つの契約から排除する。
Case II の深度・原始性・非分岐条件は既存の整数入口と実降下が復元する。 -/
theorem not_int_solution_of_phase_contracts
    (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p) (hodd : Odd p)
    (provider : CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger)
    (C : RegularDescent.Conditions (cyclotomicRamifiedPhase hζ hodd))
    {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hcop : IsCoprime a b) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  by_cases hsecond : (p : ℤ) ∣ a * b * c
  · obtain ⟨m, hm, hstate⟩ := positive_state_of_second_case
      (cyclotomicRamifiedPhase hζ hodd) hodd ha hb hc heq hcop hsecond
    exact RegularDescent.no_state C m hm hstate
  · exact not_int_solution_caseI_using hζ hp5 provider hcop hsecond heq

/-- 非零整数上の FLT。gcd 原始化で符号・共通因子の制限を除去する。
`FermatLastTheoremWith ℤ p` に含まれる a≠0,b≠0,c≠0 は除去しない。 -/
theorem fermatLastTheoremWith_int_of_phase_contracts
    (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p) (hodd : Odd p)
    (provider : CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger)
    (C : RegularDescent.Conditions (cyclotomicRamifiedPhase hζ hodd)) :
    FermatLastTheoremWith ℤ p := by
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd heq
  have hcop : IsCoprime a b := by
    apply isCoprime_of_gcd_eq_one_of_FLT (c := -c)
    · simpa only [Finset.gcd_insert, Finset.gcd_singleton, id_eq,
        ← Int.coe_gcd, Int.gcd_neg, Int.gcd_zero_right, ← Int.abs_eq_normalize, abs_neg] using hgcd
    · rw [hodd.neg_pow]
      linear_combination heq
  exact not_int_solution_of_phase_contracts hζ hp5 hodd provider C ha hb hc hcop heq


/-- 非零自然数の標準 FLT 述語。供給証明を交換してもこの終端の型は一定である。 -/
theorem fermatLastTheoremFor_of_phase_contracts
    (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p) (hodd : Odd p)
    (provider : CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger)
    (C : RegularDescent.Conditions (cyclotomicRamifiedPhase hζ hodd)) :
    FermatLastTheoremFor p :=
  fermatLastTheoremFor_iff_int.mpr
    (fermatLastTheoremWith_int_of_phase_contracts hζ hp5 hodd provider C)

end DkMath.FLT.Kummer
