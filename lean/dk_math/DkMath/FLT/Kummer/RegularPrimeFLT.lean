/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNCaseIObstruction
import DkMath.FLT.Kummer.RegularKummerUnit
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import Mathlib.NumberTheory.FLT.Basic

#print "file: DkMath.FLT.Kummer.RegularPrimeFLT"

/-!
# 正則素数 p ≥ 5 の GN–Kummer FLT

整数反例を原始化した後、`p∣abc` を判定する。
Case I は共役 packet と位相係数剛性で終了する。
Case II は整数の向き付けから正深度 State に入り、既存の共通降下で終了する。
両方で同じ円分体と類数条件を用い、深度0の State の排除は要求しない。

ここでいう正則性は、選んだ p 次円分整数環の類数と p が互いに素であること。
Kummer 単元 criterion は別仮定にせず、既に証明した一般補題から供給する。
p=3 の Case I は4項の台の議論では扱えないので、この入口は p≥5 に限定する。
-/

namespace DkMath.FLT.Kummer

open DkMath.Lib.NumberTheory
open scoped NumberField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- 一般正則素数の原始整数反例を二つの独立した終端で排除する。
正深度の Case II と、係数剛性の Case I の接続点である。 -/
theorem not_int_solution_regular_prime
    (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hcop : IsCoprime a b) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  by_cases hsecond : (p : ℤ) ∣ a * b * c
  · have hodd := hp.out.odd_of_ne_two (by omega)
    let P := cyclotomicRamifiedPhase hζ hodd
    have C : RegularDescent.Conditions P := {
      odd := hodd
      three_le := by omega
      ramification := cyclotomicRamifiedPhase_prime_dvd hζ hodd
      class_group := classGroupPTorsionFreeAt_of_coprime_card hreg
      unit_power := regular_kummer_unit_power_criterion (by omega) hreg }
    obtain ⟨m, hm, hstate⟩ := positive_state_of_second_case P hodd ha hb hc heq hcop hsecond
    exact RegularDescent.no_state C m hm hstate
  · exact not_int_solution_caseI hζ hp5 hreg hcop hsecond heq

/-- 全整数の入口。Mathlib の gcd 原始化は方程式・非零性を保持する一般補題。
その後の原始性は、共通素因子が右辺も割るという初等的議論で証明する。 -/
theorem fermatLastTheoremWith_int_of_regular_prime
    (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    FermatLastTheoremWith ℤ p := by
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd heq
  have hcop : IsCoprime a b := by
    apply isCoprime_of_gcd_eq_one_of_FLT (c := -c)
    · simpa only [Finset.gcd_insert, Finset.gcd_singleton, id_eq,
        ← Int.coe_gcd, Int.gcd_neg, Int.gcd_zero_right, ← Int.abs_eq_normalize, abs_neg] using hgcd
    · have hodd := hp.out.odd_of_ne_two (by omega)
      rw [hodd.neg_pow]
      linear_combination heq
  exact not_int_solution_regular_prime hζ hp5 hreg ha hb hc hcop heq

/-- 自然数の標準 FLT 述語への入口。完成済みの指数別 FLT は使用せず、
整数版と自然数版の一般的な同値だけを使う。 -/
theorem fermatLastTheoremFor_of_regular_prime
  (hζ : IsPrimitiveRoot ζ p)
  (hp5 : 5 ≤ p)
  (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
  FermatLastTheoremFor p :=
  fermatLastTheoremFor_iff_int.mpr (fermatLastTheoremWith_int_of_regular_prime hζ hp5 hreg)

end DkMath.FLT.Kummer
