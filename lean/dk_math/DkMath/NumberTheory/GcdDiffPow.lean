/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Algebra.DiffPow

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

/-!
素因子補題：もし素数 p が `a - b` と `diffPowSum (a,b,d)` 両方を割るなら、かつ `gcd a b = 1` のとき p は d を割る。
これは `gcd (a-b, S_d(a,b)) | d` の核心部分となる補題である。
-/

/-- 主補題（素数版）:
もし `p` が素数で `(p : ℤ)` が `a - b` と `diffPowSum a b d` の両方を割るなら、
`gcd a b = 1` の下で `p` は `d` を割る。 -/
theorem prime_dividing_gcd_divides_d {p : ℕ} (hp : p.Prime) {a b : ℤ} {d : ℕ}
    (hab : Int.gcd a b = 1)
    (hpdiv : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d)) :
    (p : ℕ) ∣ d := by
  -- let pp be the integer prime
  let pp : ℤ := p
  -- from hpdiv and gcd divisibility, pp divides a - b and S := diffPowSum a b d
  have g_dvd_left := Int.gcd_dvd_left (a - b) (diffPowSum a b d)
  have g_dvd_right := Int.gcd_dvd_right (a - b) (diffPowSum a b d)
  have pp_dvd_ab : pp ∣ (a - b) := by
    apply Int.dvd_trans hpdiv g_dvd_left
  have pp_dvd_S : pp ∣ diffPowSum a b d := by
    apply Int.dvd_trans hpdiv g_dvd_right
  -- Let S := diffPowSum a b d for brevity
  let S := diffPowSum a b d
  -- Show (a - b) divides S - d * b^(d-1):
  -- S - d*b^(d-1) = ∑_{i=0}^{d-1} (a^{d-1-i} b^i - b^{d-1})
  have S_minus_eq : S - (d : ℤ) * b ^ (d - 1)
    = ∑ i ∈ Finset.range d, (a ^ (d - 1 - i) * b ^ i - b ^ (d - 1)) := by
    -- expand the definition of S and rewrite the constant sum
    -- diffPowSum_sub_const_mul
    change (∑ i ∈ range d, a ^ (d - 1 - i) * b ^ i) - (d : ℤ) * b ^ (d - 1)
      = ∑ i ∈ Finset.range d, (a ^ (d - 1 - i) * b ^ i - b ^ (d - 1))
    have : (d : ℤ) * b ^ (d - 1) = ∑ i ∈ range d, b ^ (d - 1) := by
      simp [Finset.sum_const, Finset.card_range]
    rw [this]
    simp only [Finset.sum_sub_distrib]
  -- each term a^(m) - b^(m) is divisible by a - b
  have term_div : ∀ i ∈ range d, (a - b) ∣ (a ^ (d - 1 - i) - b ^ (d - 1 - i)) := by
    intro i hi
    have eq := pow_sub_pow_factor (a := a) (b := b) (d := d - 1 - i)
    rw [eq]
    simp
  -- multiply by b^i to get divisibility of each summand and sum up
  have : (a - b) ∣ (S - (d : ℤ) * b ^ (d - 1)) := by
    rw [S_minus_eq]
    apply Finset.dvd_sum
    intro i hi
    -- b^i * (a^{m} - b^{m}) is divisible by a - b
    have hterm := term_div i hi
    have hle : i ≤ d - 1 := by
      have hlt : i < d := by exact Finset.mem_range.mp hi
      exact Nat.le_pred_of_lt hlt
    have hpow : b ^ (d - 1) = b ^ (d - 1 - i) * b ^ i := by
      have eq : (d - 1) = (d - 1 - i) + i := by omega
      calc b ^ (d - 1) = b ^ ((d - 1 - i) + i) := by congr 1
        _ = b ^ (d - 1 - i) * b ^ i := by rw [pow_add]
    have heq : a ^ (d - 1 - i) * b ^ i - b ^ (d - 1)
          = b ^ i * (a ^ (d - 1 - i) - b ^ (d - 1 - i)) := by
      rw [hpow]
      ring
    rw [heq]
    have hmul := dvd_mul_of_dvd_left hterm (b ^ i)
    simpa [mul_comm] using hmul
  -- since pp divides a-b and S, subtracting shows pp divides d * b^(d-1)
  have pp_dvd_d_mul_bpow : pp ∣ (d : ℤ) * b ^ (d - 1) := by
    -- pp divides S and pp divides S - d*b^(d-1), therefore pp divides their difference d*b^(d-1)
    have pp_div_Sminus : pp ∣ (S - (d : ℤ) * b ^ (d - 1)) := by
      apply Int.dvd_trans pp_dvd_ab
      exact this
    -- simplify the subtraction to get d*b^(d-1)
    have hsub := Int.dvd_sub pp_dvd_S pp_div_Sminus
    have eq : (d : ℤ) * b ^ (d - 1) = S - (S - (d : ℤ) * b ^ (d - 1)) := by ring
    rw [eq]
    exact hsub
  -- show pp cannot divide b (otherwise divides a as well, contradicting gcd a b = 1)
  have pp_not_dvd_b : ¬ pp ∣ b := by
    intro h
    -- if pp ∣ b and pp ∣ a - b then pp ∣ a
    have pa : pp ∣ a := by simpa using Int.dvd_add pp_dvd_ab h
    -- from pa and h we obtain a natural-number divisibility p ∣ gcd a b
    have gg_nat : p ∣ Int.gcd a b := Int.dvd_gcd pa h
    -- hence p divides 1 (since gcd a b = 1), contradiction with primality
    have : p ∣ 1 := by rwa [hab] at gg_nat
    exact hp.not_dvd_one this
  -- convert integer divisibility to nat-level and use primality: p ∣ d * b.natAbs^(d-1)
  have nat_mul_dvd : (p : ℕ) ∣ d * (b.natAbs ^ (d - 1)) := by
    rcases pp_dvd_d_mul_bpow with ⟨k, hk⟩
    -- take absolute values of both sides and simplify stepwise
    have habs := congrArg Int.natAbs hk
    have eq1 : p * k.natAbs = Int.natAbs (d * b ^ (d - 1)) := by
      calc
        p * k.natAbs = Int.natAbs pp * k.natAbs := by simp [pp]
        _ = Int.natAbs (pp * k) := by rw [Int.natAbs_mul]
        _ = Int.natAbs (d * b ^ (d - 1)) := by exact habs.symm
    have eq2 : Int.natAbs (d * b ^ (d - 1)) = d * (b.natAbs ^ (d - 1)) := by
      calc
        Int.natAbs (d * b ^ (d - 1))
          = Int.natAbs (d : ℤ) * Int.natAbs (b ^ (d - 1)) := by simp [Int.natAbs_mul]
        _ = Int.natAbs (d : ℤ) * (b.natAbs ^ (d - 1)) := by simp [Int.natAbs_pow]
        _ = d * (b.natAbs ^ (d - 1)) := by
          have : Int.natAbs (d : ℤ) = d := by
            induction d with
            | zero => simp
            | succ _ => omega
          rw [this]
    have eq : p * k.natAbs = d * (b.natAbs ^ (d - 1)) := by
      calc
        p * k.natAbs = Int.natAbs (d * b ^ (d - 1)) := eq1
        _ = d * (b.natAbs ^ (d - 1)) := eq2
    use k.natAbs
    simp [eq]
  -- since p is prime, p ∣ d or p ∣ b.natAbs^(d-1);
  -- the latter implies p ∣ b (contradiction), so p ∣ d
  have : (p : ℕ) ∣ d := by
    rcases (hp.dvd_mul.mp nat_mul_dvd) with (pd | pbpow)
    · exact pd
    -- helper: prime divides power => prime divides base (simple induction)
    have prime_divides_pow : ∀ n, (p : ℕ) ∣ (b.natAbs ^ n) → (p : ℕ) ∣ b.natAbs := by
      intro n
      induction n with
      | zero => intro h; exact False.elim (hp.not_dvd_one h)
      | succ n ih =>
        intro h
        rw [pow_succ] at h
        have hd := hp.dvd_mul.mp h
        rcases hd with (h1 | h2)
        · exact ih h1
        · exact h2
    · -- derive p ∣ b.natAbs from p ∣ b.natAbs^(d-1)
      have pb : (p : ℕ) ∣ b.natAbs := by
        exact prime_divides_pow (d - 1) pbpow
      -- pb : p ∣ b.natAbs, derive pp ∣ b as integer then contradiction
      rcases pb with ⟨m, hm⟩
      let bm : ℤ := (b.sign : ℤ) * (m : ℤ)
      have h1 := (Int.sign_mul_natAbs b).symm
      have h2 : (b.sign : ℤ) * ↑(b.natAbs) = pp * bm := by
        calc
          (b.sign : ℤ) * ↑(b.natAbs) = (b.sign : ℤ) * ↑(p * m) := by rw [hm]
          _ = pp * bm := by
            have : ↑(p * m) = pp * (m : ℤ) := by simp [pp]
            rw [this]
            ring
      have : b = pp * bm := by rw [h1, h2]
      have pp_div_b : pp ∣ b := by use bm
      have : False := pp_not_dvd_b pp_div_b
      exact False.elim this
  -- done: (p : ℕ) ∣ d
  exact this



/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    ( (a - b).natAbs.gcd (diffPowSum a b d).natAbs ) ∣ d := by
  -- strong induction on the gcd (handle N = 0 separately)
  let N := (a - b).natAbs.gcd (diffPowSum a b d).natAbs
  by_cases hN : N = 0
  · -- N = 0 leads to contradiction with hab
    have ⟨ha0, hb0⟩ := Nat.gcd_eq_zero_iff.1 hN
    have h_diff_zero : a - b = 0 := Int.natAbs_eq_zero.1 ha0
    have hS_zero : diffPowSum a b d = 0 := Int.natAbs_eq_zero.1 hb0
    have h_a_eq_b : a = b := by linarith [h_diff_zero]
    have S_eq : diffPowSum a b d = (d : ℤ) * b ^ (d - 1) := by
      unfold diffPowSum
      -- when a = b, each summand simplifies to b^(d - 1)
      have term_eq : ∀ i ∈ range d, a ^ (d - 1 - i) * b ^ i = b ^ (d - 1) := by
        intro i hi
        have hlt : i < d := Finset.mem_range.mp hi
        -- rewrite a to b and use (d - 1 - i) + i = d - 1
        rw [h_a_eq_b]
        have hsum : (d - 1 - i) + i = d - 1 := by
          apply Nat.sub_add_cancel
          exact Nat.le_pred_of_lt hlt
        calc
          b ^ (d - 1 - i) * b ^ i = b ^ ((d - 1 - i) + i) := by rw [pow_add]
          _ = b ^ (d - 1) := by rw [hsum]
      have : ∑ i ∈ range d, a ^ (d - 1 - i) * b ^ i = ∑ i ∈ range d, b ^ (d - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact term_eq i hi
      rw [this]
      simp [Finset.sum_const, Finset.card_range]
      done
    have hprod : (d : ℤ) * b ^ (d - 1) = 0 := by
      rw [S_eq] at hS_zero
      exact hS_zero
    have habs := congrArg Int.natAbs hprod
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow] at habs
    have h_mul_zero : d * (b.natAbs ^ (d - 1)) = 0 := by simpa using habs
    have h_b_nat_zero : b.natAbs = 0 := by
      have hd_nonzero : d ≠ 0 := by linarith [hd]
      rw [Nat.mul_eq_zero] at h_mul_zero
      match h_mul_zero with
      | Or.inl h_d_zero =>
        exfalso
        exact hd_nonzero h_d_zero
      | Or.inr h_b_zero =>
        -- pow_eq_zero_iff: b.natAbs ^ (d - 1) = 0 ↔ b.natAbs = 0 ∨ d - 1 = 0
        -- Nat.pow_eq_zero: b.natAbs ^ (d - 1) = 0 ↔ b.natAbs = 0 ∨ d - 1 = 0
        rw [Nat.pow_eq_zero] at h_b_zero
        -- pow_eq_zero_iff: b.natAbs ^ (d - 1) = 0 ↔ b.natAbs = 0 ∧ (d - 1) ≠ 0
        -- ただし d - 1 = 0 なら b.natAbs ^ 0 = 1 ≠ 0 なので矛盾
        by_cases h_exp_zero : d - 1 = 0
        · -- d - 1 = 0 ⇒ d = 1, この場合 h_mul_zero より 1 * 1 = 0 となり矛盾
          have hd1 : d = 1 := by omega
          rw [hd1] at h_mul_zero
          simp at h_mul_zero
        · -- それ以外は b.natAbs = 0 のみ
          exact h_b_zero.left
      done
    have h_b_zero : b = 0 := by simpa [Int.natAbs_eq_zero] using h_b_nat_zero
    have h_a_zero : a = 0 := by simp [h_a_eq_b, h_b_zero]
    -- rewrite hab using a = 0, b = 0 to get contradiction
    rw [h_a_zero, h_b_zero] at hab
    simp at hab
  · -- N ≥ 1, prove the divisibility by strong induction on positive n
    have N_pos : 1 ≤ N := by
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
    refine Nat.strong_induction_on N ?_
    intro n IH
    cases n with
    | zero =>
      -- n = 0 leads to contradiction with hab
      have eqN : (a - b).natAbs.gcd (diffPowSum a b d).natAbs = 0 := by simpa [N] using rfl
      have ⟨ha0, hb0⟩ := Nat.gcd_eq_zero_iff.1 eqN
      have ha : a - b = 0 := by simpa [ha0] using rfl
      have hb : diffPowSum a b d = 0 := by simpa [hb0] using rfl
      have : a = b := by linarith [ha]
      have S_eq : diffPowSum a b d = (d : ℤ) * b ^ (d - 1) := by
        unfold diffPowSum
        simp [ha, Finset.sum_const, Finset.card_range]
      have hprod : (d : ℤ) * b ^ (d - 1) = 0 := by simpa [S_eq, hb] using rfl
      have habs := congrArg Int.natAbs hprod
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow] at habs
      have hmul : d * (b.natAbs ^ (d - 1)) = 0 := by simpa using habs
      have hb_nat_zero : b.natAbs = 0 := by
        rcases (Nat.mul_eq_zero).mp hmul with hd0 | hb0
        · have : d = 0 := hd0; linarith [hd]
        · exact hb0
      have : b = 0 := by simpa [Int.natAbs_eq_zero] using hb_nat_zero
      have : a = 0 := by linarith [this]
      have : Int.gcd a b = 0 := by simp [this]
      simp [hab] at this
      done
    | succ n' =>
      by_cases hn1 : n' = 0
      · -- n = 1
        exact one_dvd d
      · -- n ≥ 2
        let n := n' + 1
        have hnpos : 1 < n := by linarith [hn1]
        obtain ⟨p, hp, pdivn⟩ := Nat.exists_prime_and_dvd hnpos
        have pd1 : p ∣ (a - b).natAbs := by apply Nat.dvd_trans pdivn (Nat.gcd_dvd_left _ _)
        have pd2 : p ∣ (diffPowSum a b d).natAbs := by apply Nat.dvd_trans pdivn (Nat.gcd_dvd_right _ _)
        have pint : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) := by
          have : (p : ℤ) ∣ (a - b) := by simpa using Int.dvd_natAbs.2 pd1
          have : (p : ℤ) ∣ diffPowSum a b d := by simpa using Int.dvd_natAbs.2 pd2
          exact Int.dvd_gcd this this
        have pdivd : (p : ℕ) ∣ d := by apply prime_dividing_gcd_divides_d hp hab; simpa using pint
        let m := n / p
        have m_lt : m < n := Nat.div_lt_self (by linarith [hp.one_lt]) (by linarith [hnpos])
        have m_ne_zero : m ≠ 0 := by
          intro hm
          have eqnm : n = p * m := by simp [n, m, Nat.mul_div_cancel' pdivn]
          have n_zero : n = 0 := by simpa [hm] using eqnm
          linarith [hnpos, n_zero]
        have m_ge1 : 1 ≤ m := by
          have mpos : 0 < m := Nat.pos_of_ne_zero m_ne_zero
          exact Nat.succ_le_iff.mpr mpos
        have m_dvd : m ∣ d := by apply IH m m_lt m_ge1
        have : n = p * m := by simp [n, m, Nat.mul_div_cancel' pdivn]
        exact Nat.mul_dvd_mul pdivd m_dvd
      done  --
    done
  done



/-- 主定理：|a-b| と |S| の整数 gcd が d を割る。 -/
theorem gcd_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    Int.gcd (a - b) (diffPowSum a b d) ∣ d := by
  set g := (Int.gcd (a - b) (diffPowSum a b d) : ℤ)
  have g_dvd_S := Int.gcd_dvd_right (a - b) (diffPowSum a b d)
  have g_dvd_ab := Int.gcd_dvd_left (a - b) (diffPowSum a b d)
  -- show g ∣ d * b^(d-1)
  have S_minus_eq : diffPowSum a b d - (d : ℤ) * b ^ (d - 1)
    = ∑ i ∈ range d, (a ^ (d - 1 - i) * b ^ i - b ^ (d - 1)) := by
    unfold diffPowSum
    have : (d : ℤ) * b ^ (d - 1) = ∑ i ∈ range d, b ^ (d - 1) := by
      simp [Finset.sum_const, Finset.card_range]
    rw [this]
    simp [Finset.sum_sub_distrib]
  have ab_div := by
    have : (a - b) ∣ (diffPowSum a b d - (d : ℤ) * b ^ (d - 1)) := by
      rw [S_minus_eq]
      apply Finset.dvd_sum
      intro i hi
      have hle : i ≤ d - 1 := by
        have hlt : i < d := by exact Finset.mem_range.mp hi
        exact Nat.le_pred_of_lt hlt
      have hpow : b ^ (d - 1) = b ^ (d - 1 - i) * b ^ i := by
        have eq : (d - 1) = (d - 1 - i) + i := by omega
        calc b ^ (d - 1) = b ^ ((d - 1 - i) + i) := by congr 1
          _ = b ^ (d - 1 - i) * b ^ i := by rw [pow_add]
      have heq : a ^ (d - 1 - i) * b ^ i - b ^ (d - 1)
        = b ^ i * (a ^ (d - 1 - i) - b ^ (d - 1 - i)) := by
        rw [hpow]; ring
      rw [heq]
      have eq := pow_sub_pow_factor (a := a) (b := b) (d := d - 1 - i)
      have : (a - b) ∣ (a ^ (d - 1 - i) - b ^ (d - 1 - i)) := by
        rw [eq]; simp
      have hmul := dvd_mul_of_dvd_left this (b ^ i)
      simpa [mul_comm] using hmul
    exact this
  -- Use natural-level gcd lemma directly to finish
  rcases gcd_natAbs_divides_d hd hab with ⟨k, hk⟩
  -- use the basic lemma `gcd_eq_natAbs` (available from Mathlib) to relate integer gcd to nat gcd
  have h := Int.gcd_eq_natAbs (a := a - b) (b := diffPowSum a b d)
  have eqN : Int.gcd (a - b) (diffPowSum a b d)
    = ((a - b).natAbs.gcd (diffPowSum a b d).natAbs : ℤ) := by simpa using h.symm
  use k
  have eq_nat : (Int.gcd (a - b) (diffPowSum a b d) : ℕ)
    = (a - b).natAbs.gcd (diffPowSum a b d).natAbs := by
    exact Int.natAbs_gcd (a - b) (diffPowSum a b d)
  have h_cast : (Int.gcd (a - b) (diffPowSum a b d) : ℤ) * ↑k = ↑d := by
    have eq := congrArg (fun (x : ℕ) => (x : ℤ)) hk
    simp only [Nat.cast_mul] at eq
    exact eq.symm
  have h_eq : d = (a - b).gcd (diffPowSum a b d) * k := by
    have : (d : ℤ) = ((a - b).gcd (diffPowSum a b d) : ℤ) * ↑k := h_cast.symm
    have : d = (a - b).gcd (diffPowSum a b d) * k := by omega
    exact this
  exact h_eq


end DkMath.NumberTheory.GcdDiffPow
