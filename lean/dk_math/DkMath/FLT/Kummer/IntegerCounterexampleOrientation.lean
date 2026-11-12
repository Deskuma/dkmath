/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under Apache-2.0; see DkMath/Lib/NumberTheory/RegularKummer/LICENSE.
The two-congruence lemma is adapted from leanprover-community/flt-regular,
b8a5f23ab44a7be9fd49f6e3c831da54573c3c89, FltRegular/MayAssume/Lemmas.lean.
-/

import DkMath.FLT.Kummer.RegularStateTransport
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.FLT.Kummer.IntegerCounterexampleOrientation"

/-!
# 整数反例の向き付け

奇数冪では負号を根へ戻せる。右辺が p で割れる Case II の形へ
変数を移すとき、原始性・非零性・左側の非分岐性を同時に運ぶ。
Case I では `a≡b` の例外を `(a,-c,-b)` への移動で解消する。
整数のこの操作は円分体や正則性を必要としない。
-/

namespace DkMath.FLT.Kummer

open Int

/-- 原始的な冪和方程式の右辺は、左辺の各変数と互いに素。
冪の互いに素性と和の保存から導き、共通因子を捨てる操作はしない。 -/
theorem coprime_right_of_flt_equation {p : ℕ} (hp : 0 < p) {a b c : ℤ}
    (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b) :
    IsCoprime a c ∧ IsCoprime b c := by
  have hac : IsCoprime (a ^ p) (c ^ p) := by
    convert (hcop.pow (m := p) (n := p)).add_mul_left_right 1 using 1
    rw [mul_one, add_comm, heq]
  have hbc : IsCoprime (b ^ p) (c ^ p) := by
    convert (hcop.symm.pow (m := p) (n := p)).add_mul_left_right 1 using 1
    rw [mul_one, heq]
  exact ⟨(IsCoprime.pow_iff hp hp).mp hac, (IsCoprime.pow_iff hp hp).mp hbc⟩

/-- a≡b かつ b≡−c なら、Fermat の合同式は 3c≡0 となる。
p≠3 を明示し、Case I の向き付けで必要な例外処理を分離する。 -/
theorem prime_dvd_right_of_two_congruences {p : ℕ} {a b c : ℤ} (hpri : p.Prime)
    (hp : p ≠ 3) (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p])
    (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by
  have : Fact p.Prime := ⟨hpri⟩
  replace h := congr_arg (fun n : ℤ => (n : ZMod p)) h
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at h
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_neg] at hbc hab
  rw [hab, hbc, ← sub_eq_zero, ← sub_eq_add_neg, ← Int.cast_neg, ← Int.cast_sub,
    ← Int.cast_sub] at h
  ring_nf at h
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, neg_eq_zero, mul_eq_zero] at h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine Or.resolve_right h fun h3 ↦ ?_
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_zero_iff,
    Nat.dvd_prime Nat.prime_three] at h3
  exact h3.elim hpri.ne_one hp

/-- p≥5 の原始的 Case I 反例を、左の二変数が非合同な形へ移す。
元の変数が合同なら `(a,-c,-b)` を使う。新しい原始性も方程式から証明する。 -/
theorem orient_first_case {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧ IsCoprime x y ∧
      ¬ Int.ModEq p x y ∧ ¬ (p : ℤ) ∣ x * y * z := by
  by_cases hab : Int.ModEq p a b
  · refine ⟨a, -c, -b, ?_, ?_, ?_, ?_⟩
    · have hodd := hp.out.odd_of_ne_two (by omega)
      rw [hodd.neg_pow, hodd.neg_pow]
      linear_combination heq
    · exact (coprime_right_of_flt_equation hp.out.pos heq hcop).1.neg_right
    · intro hac
      have hbc := hab.symm.trans hac
      have hc := prime_dvd_right_of_two_congruences hp.out (by omega) heq hab hbc
      exact hfirst (dvd_mul_of_dvd_right hc _)
    · have hprod : a * -c * -b = a * b * c := by ring
      simpa only [hprod] using hfirst
  · exact ⟨a, b, c, heq, hcop, hab, hfirst⟩

/-- 原始的 Case II の反例を正深度 State の整数入口へ向ける。
p が a・b・c のどれを割るかを尽くし、右辺の非零性と左第二変数の
非分岐性を保持する。深度0の State に関する主張は含まない。 -/
theorem orient_second_case {p : ℕ} [hp : Fact p.Prime] (hodd : Odd p)
    {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b)
    (hsecond : (p : ℤ) ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧ IsCoprime x y ∧
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ∣ y := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨hac, hbc⟩ := coprime_right_of_flt_equation hp.out.pos heq hcop
  have away {x y : ℤ} (hxy : IsCoprime x y) (hx : (p : ℤ) ∣ x) : ¬ (p : ℤ) ∣ y :=
    fun hy => hprime.not_isUnit (hxy.isUnit_of_dvd' hx hy)
  rcases hprime.dvd_mul.mp hsecond with hab | hpc
  · rcases hprime.dvd_mul.mp hab with hpa | hpb
    · refine ⟨b, -c, -a, ?_, hbc.neg_right, hb, neg_ne_zero.mpr hc,
        neg_ne_zero.mpr ha, dvd_neg.mpr hpa, ?_⟩
      · rw [hodd.neg_pow, hodd.neg_pow]
        linear_combination heq
      · simpa only [dvd_neg] using away hac hpa
    · refine ⟨a, -c, -b, ?_, hac.neg_right, ha, neg_ne_zero.mpr hc,
        neg_ne_zero.mpr hb, dvd_neg.mpr hpb, ?_⟩
      · rw [hodd.neg_pow, hodd.neg_pow]
        linear_combination heq
      · simpa only [dvd_neg] using away hbc hpb
  · exact ⟨a, b, c, heq, hcop, ha, hb, hc, hpc, away hbc.symm hpc⟩

/-- 向き付けた整数反例を既存の正深度 State へ接続する。
State の x,y は選んだ同じ整数 x,y の像で、原始性をそのまま運ぶ。 -/
theorem positive_state_of_second_case
    {R : Type*} [CommRing R] [IsDedekindDomain R] [CharZero R]
    {p : ℕ} [Fact p.Prime] (P : DkMath.Lib.NumberTheory.RamifiedPhasePacket R p)
    (hodd : Odd p) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b)
    (hsecond : (p : ℤ) ∣ a * b * c) :
    ∃ m, 1 ≤ m ∧ Nonempty (RegularDescent.State P m) := by
  obtain ⟨x, y, z, h, hxy, _, _, hz, hpz, hpy⟩ :=
    orient_second_case hodd ha hb hc heq hcop hsecond
  exact RegularDescent.initial_state_of_int_solution P hz h hxy hpz hpy

end DkMath.FLT.Kummer
