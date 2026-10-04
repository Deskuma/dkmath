/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCyclotomic
import DkMath.NumberTheory.GapFocusing.CyclotomicAddress
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.NumberTheory.Multiplicity

#print "file: DkMath.NumberTheory.GapFocusing.LayerValuation"

/-!
# Valuation along prime-power degree inflation

The power-difference formula is an LTE statement. The cyclotomic formulas
below are restricted to prime-power indices at the unit anchor. They distinguish
the first `2`-layer from the higher `2`-power layers, and do not infer a
valuation bound from primitive-prime freshness.
-/

open scoped BigOperators

namespace DkMath.NumberTheory.GapFocusing

open DkMath.Lib.NumberTheory

/-- At the fundamental order address, the layer retains the complete
power-difference valuation. No upper bound on that valuation is asserted. -/
theorem padicValInt_cyclotomicEval_eq_pow_sub_one_of_orderOf_eq
    {q n : ℕ} [Fact q.Prime] (a : ℤ) (hn : 0 < n)
    (horder : orderOf (a : ZMod q) = n) (hdiff : a ^ n - 1 ≠ 0) :
    padicValInt q (cyclotomicEval n a) = padicValInt q (a ^ n - 1) := by
  have hq : q.Prime := Fact.out
  have hqInt : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hprod : (∏ m ∈ n.divisors, cyclotomicEval m a) = a ^ n - 1 := by
    have hpoly := congrArg (Polynomial.eval a)
      (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
    simpa [cyclotomicEval, Polynomial.eval_prod] using hpoly
  have hfactor : (∏ m ∈ n.divisors.erase n, cyclotomicEval m a) *
      cyclotomicEval n a = a ^ n - 1 := by
    rw [Finset.prod_erase_mul _ _ (Nat.mem_divisors_self n hn.ne')]
    exact hprod
  have hnot : ¬ (q : ℤ) ∣ ∏ m ∈ n.divisors.erase n, cyclotomicEval m a := by
    intro h
    obtain ⟨m, hm, hdiv⟩ := (hqInt.dvd_finsetProd_iff _).mp h
    have hmdiv := (Finset.mem_erase.mp hm).2
    have hmpos := Nat.pos_of_mem_divisors hmdiv
    have hmlt : m < n := lt_of_le_of_ne
      (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hmdiv)) (Finset.mem_erase.mp hm).1
    obtain ⟨k, hmk⟩ :=
      (prime_dvd_cyclotomicEval_iff_prime_pow_mul_orderOf hmpos a).mp hdiv
    rw [horder] at hmk
    have hnle : n ≤ m := by
      rw [hmk]
      exact Nat.le_mul_of_pos_right _ (pow_pos hq.pos k)
    omega
  have hp0 : (∏ m ∈ n.divisors.erase n, cyclotomicEval m a) ≠ 0 := by
    intro hz
    exact hnot (hz ▸ dvd_zero (q : ℤ))
  have he0 : cyclotomicEval n a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfactor
    exact hdiff hfactor.symm
  have hval := congrArg (padicValInt q) hfactor
  rw [padicValInt.mul hp0 he0, padicValInt.eq_zero_of_not_dvd hnot, zero_add] at hval
  exact hval

/-- LTE after any base degree whose power difference is divisible by an odd prime. -/
theorem padicValNat_pow_sub_pow_mul_prime_pow
    {q a b r : ℕ} (hq : q.Prime) (hqodd : Odd q) (hab : b < a)
    (hr : r ≠ 0) (hqar : ¬ q ∣ a) (hqdiff : q ∣ a ^ r - b ^ r) (k : ℕ) :
    padicValNat q (a ^ (r * q ^ k) - b ^ (r * q ^ k)) =
      padicValNat q (a ^ r - b ^ r) + k := by
  let : Fact q.Prime := ⟨hq⟩
  have hqar' : ¬ q ∣ a ^ r := by
    intro h
    exact hqar (hq.dvd_of_dvd_pow h)
  simpa only [← pow_mul, padicValNat.prime_pow] using
    padicValNat.pow_sub_pow hqodd (Nat.pow_lt_pow_left hab hr) hqdiff hqar'
      (pow_ne_zero k hq.ne_zero)

/-- At prime `2`, positive degree inflation carries a sum correction term. -/
theorem padicValNat_pow_sub_pow_mul_two_pow_succ
    {a b r : ℕ} (hab : b < a) (hr : r ≠ 0) (haodd : ¬ 2 ∣ a)
    (hdiff : 2 ∣ a ^ r - b ^ r) (k : ℕ) :
    padicValNat 2 (a ^ (r * 2 ^ (k + 1)) - b ^ (r * 2 ^ (k + 1))) =
      padicValNat 2 (a ^ r + b ^ r) + padicValNat 2 (a ^ r - b ^ r) + k := by
  have hpa : ¬ 2 ∣ a ^ r := fun h => haodd (Nat.prime_two.dvd_of_dvd_pow h)
  have h := padicValNat.pow_two_sub_pow (Nat.pow_lt_pow_left hab hr) hdiff hpa
    (pow_ne_zero (k + 1) (by decide : (2 : ℕ) ≠ 0))
    (even_two.pow_of_ne_zero (by omega : k + 1 ≠ 0))
  simp only [← pow_mul, padicValNat.prime_pow] at h
  omega

/-- The integral prime-power cyclotomic value is a natural geometric sum. -/
theorem natAbs_cyclotomicEval_prime_pow (q a k : ℕ) (hq : q.Prime) :
    (cyclotomicEval (q ^ (k + 1)) (a : ℤ)).natAbs =
      ∑ i ∈ Finset.range q, (a ^ (q ^ k)) ^ i := by
  have hcast : cyclotomicEval (q ^ (k + 1)) (a : ℤ) =
      ((∑ i ∈ Finset.range q, (a ^ (q ^ k)) ^ i : ℕ) : ℤ) := by
    simp [cyclotomicEval, Polynomial.cyclotomic_prime_pow_eq_geom_sum hq,
      Polynomial.eval₂_finsetSum]
  rw [hcast, Int.natAbs_natCast]

/-- Evaluated prime-power cyclotomic factors recover the corresponding power difference. -/
theorem natAbs_cyclotomicEval_prime_pow_mul_sub_one
    (q a k : ℕ) (hq : q.Prime) (ha : 1 < a) :
    (cyclotomicEval (q ^ (k + 1)) (a : ℤ)).natAbs * (a ^ (q ^ k) - 1) =
      a ^ (q ^ (k + 1)) - 1 := by
  let : Fact q.Prime := ⟨hq⟩
  rw [natAbs_cyclotomicEval_prime_pow q a k hq]
  have hz := congrArg (Polynomial.eval (a : ℤ))
    (Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one ℤ q k)
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hq] at hz
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_finsetSum] at hz
  have hlow : 1 ≤ a ^ (q ^ k) :=
    Nat.succ_le_of_lt (pow_pos (lt_trans Nat.zero_lt_one ha) _)
  have hhigh : 1 ≤ a ^ (q ^ (k + 1)) :=
    Nat.succ_le_of_lt (pow_pos (lt_trans Nat.zero_lt_one ha) _)
  exact_mod_cast hz

/-- For an odd prime dividing `a-1`, every prime-power layer has valuation exactly one. -/
theorem padicValNat_cyclotomicEval_prime_pow_eq_one
    {q a : ℕ} (hq : q.Prime) (hqodd : Odd q) (ha : 1 < a)
    (hqa : ¬ q ∣ a) (hqdiff : q ∣ a - 1) (k : ℕ) :
    padicValNat q (cyclotomicEval (q ^ (k + 1)) (a : ℤ)).natAbs = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hfactor := natAbs_cyclotomicEval_prime_pow_mul_sub_one q a k hq ha
  have hlow : a ^ (q ^ k) - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (pow_ne_zero k hq.ne_zero) ha)
  have hhigh : a ^ (q ^ (k + 1)) - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (pow_ne_zero (k + 1) hq.ne_zero) ha)
  have heval : (cyclotomicEval (q ^ (k + 1)) (a : ℤ)).natAbs ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfactor
    exact hhigh hfactor.symm
  have hvals := congrArg (padicValNat q) hfactor
  rw [padicValNat.mul heval hlow] at hvals
  have hlo := padicValNat.pow_sub_pow hqodd ha hqdiff hqa
    (pow_ne_zero k hq.ne_zero)
  have hhi := padicValNat.pow_sub_pow hqodd ha hqdiff hqa
    (pow_ne_zero (k + 1) hq.ne_zero)
  simp only [one_pow, padicValNat.prime_pow] at hlo hhi
  rw [hlo, hhi] at hvals
  omega

/-- The first `2`-layer retains the full valuation of `a+1`. -/
theorem padicValNat_cyclotomicEval_two (a : ℕ) :
    padicValNat 2 (cyclotomicEval 2 (a : ℤ)).natAbs = padicValNat 2 (a + 1) := by
  simp only [cyclotomicEval, Polynomial.cyclotomic_two, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_one]
  have hc : (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) := by simp
  rw [hc, Int.natAbs_natCast]

/-- For odd `a>1`, the later `2`-power layers have valuation exactly one. -/
theorem padicValNat_cyclotomicEval_two_pow_succ_eq_one
    {a : ℕ} (ha : 1 < a) (haodd : ¬ 2 ∣ a) (hdiff : 2 ∣ a - 1) (k : ℕ) :
    padicValNat 2 (cyclotomicEval (2 ^ (k + 2)) (a : ℤ)).natAbs = 1 := by
  have hfactor := natAbs_cyclotomicEval_prime_pow_mul_sub_one 2 a (k + 1)
    Nat.prime_two ha
  have hlow : a ^ (2 ^ (k + 1)) - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by positivity) ha)
  have hhigh : a ^ (2 ^ (k + 2)) - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by positivity) ha)
  have heval : (cyclotomicEval (2 ^ (k + 2)) (a : ℤ)).natAbs ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfactor
    exact hhigh hfactor.symm
  have hvals := congrArg (padicValNat 2) hfactor
  rw [padicValNat.mul heval hlow] at hvals
  simp only [Nat.add_assoc, Nat.reduceAdd] at hvals
  have hlo := padicValNat.pow_two_sub_pow ha hdiff haodd
    (by positivity : 2 ^ (k + 1) ≠ 0)
    (even_two.pow_of_ne_zero (by omega : k + 1 ≠ 0))
  have hhi := padicValNat.pow_two_sub_pow ha hdiff haodd
    (by positivity : 2 ^ (k + 2) ≠ 0)
    (even_two.pow_of_ne_zero (by omega : k + 2 ≠ 0))
  simp only [one_pow, padicValNat.prime_pow] at hlo hhi
  omega

end DkMath.NumberTheory.GapFocusing
