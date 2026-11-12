/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNCaseIObstruction
import DkMath.FLT.Kummer.RegularPrimeContract
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
固定契約だけを使う終端は `RegularPrimeContract` に置き、このファイルは
古典的な既定供給を渡すアダプタとする。整数版は a,b,c≠0 を必要とする。

ここでいう正則性は、選んだ p 次円分整数環の類数と p が互いに素であること。
Kummer 単元 criterion は別仮定にせず、既に証明した一般補題から供給する。
p=3 の Case I は4項の台の議論では扱えないので、この入口は p≥5 に限定する。
-/

namespace DkMath.FLT.Kummer

open DkMath.Lib.NumberTheory
open scoped NumberField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- 正則性から既定の算術条件を供給する。Conditions のフィールド型は固定し、
将来の類群・単元 criterion の別証明は同じ Conditions の値として渡す。 -/
theorem regular_prime_conditions (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    RegularDescent.Conditions (cyclotomicRamifiedPhase hζ hodd) where
  odd := hodd
  three_le := hp3
  ramification := cyclotomicRamifiedPhase_prime_dvd hζ hodd
  class_group := classGroupPTorsionFreeAt_of_coprime_card hreg
  unit_power := regular_kummer_unit_power_criterion (by omega) hreg

/-- 一般正則素数の非零な原始整数反例を排除する既定アダプタ。
共役 Packet と算術 Conditions の実供給を、固定した終端へ渡す。 -/
theorem not_int_solution_regular_prime
    (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hcop : IsCoprime a b) :
    a ^ p + b ^ p ≠ c ^ p := by
  have hodd := hp.out.odd_of_ne_two (by omega)
  exact not_int_solution_of_phase_contracts hζ hp5 hodd
    (classical_solution_packet_provider hζ hp5 hreg)
    (regular_prime_conditions hζ hodd (by omega) hreg) ha hb hc hcop

/-- a,b,c≠0 を満たす整数上の FLT。符号・共通因子を制限しない。
零を許せば `0^p+1^p=1^p` が成立するので、非零条件は本質的である。 -/
theorem fermatLastTheoremWith_int_of_regular_prime
    (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    FermatLastTheoremWith ℤ p := by
  have hodd := hp.out.odd_of_ne_two (by omega)
  exact fermatLastTheoremWith_int_of_phase_contracts hζ hp5 hodd
    (classical_solution_packet_provider hζ hp5 hreg)
    (regular_prime_conditions hζ hodd (by omega) hreg)

/-- 自然数の標準 FLT 述語への入口。完成済みの指数別 FLT は使用せず、
整数版と自然数版の一般的な同値だけを使う。 -/
theorem fermatLastTheoremFor_of_regular_prime
  (hζ : IsPrimitiveRoot ζ p)
  (hp5 : 5 ≤ p)
  (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
  FermatLastTheoremFor p :=
  fermatLastTheoremFor_iff_int.mpr (fermatLastTheoremWith_int_of_regular_prime hζ hp5 hreg)

end DkMath.FLT.Kummer
