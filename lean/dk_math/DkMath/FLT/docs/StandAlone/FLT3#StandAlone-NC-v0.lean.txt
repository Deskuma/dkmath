/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 697d62b5-312c-83a8-a917-f4aca8fa80ca

import Mathlib

set_option linter.style.longLine false

#print "DkMath.FLT.docs.StandAlone.FLT3#StandAlone-NC"

/-!
# FLT - Fermat's Last Theorem - Stand-alone lemmas for the case n=3, no coprimality assumptions
-----------------------------------------------------------------------------------------------
    Note:
        This lemma set is a formalization file for single-file builds only.
        It is forbidden to import or be imported (except by Mathlib).
-----------------------------------------------------------------------------------------------
-/

def diffPowSum {α : Type*} [CommRing α] (a b : α) (d : ℕ) : α :=
  ∑ i ∈ Finset.range d, a^(d - 1 - i) * b^i

def quotientPrimePow (a b p : ℕ) : ℕ :=
  (a^p - b^p) / (a - b)

def S0_nat (a b : ℕ) : ℕ := a^2 + a*b + b^2

lemma cube_sub_eq_of_add_eq {a b c : ℕ} (h : a ^ 3 + b ^ 3 = c ^ 3) :
    c ^ 3 - b ^ 3 = a ^ 3 := by
  rw [← h]
  omega

lemma coprime_cb_of_eq {a b c : ℕ}
    (hab : Nat.Coprime a b) (h : a ^ 3 + b ^ 3 = c ^ 3) :
    Nat.Coprime c b := by
  by_contra hnot
  have hgcd_ne : Nat.gcd c b ≠ 1 := by
    intro hg
    apply hnot
    exact (Nat.coprime_iff_gcd_eq_one).2 hg
  obtain ⟨p, hp, hp_dvd_g⟩ := Nat.exists_prime_and_dvd hgcd_ne
  have hp_dvd_c : p ∣ c := dvd_trans hp_dvd_g (Nat.gcd_dvd_left c b)
  have hp_dvd_b : p ∣ b := dvd_trans hp_dvd_g (Nat.gcd_dvd_right c b)
  have hp_dvd_c3 : p ∣ c ^ 3 := dvd_trans hp_dvd_c (dvd_pow_self c (by decide : 3 ≠ 0))
  have hp_dvd_b3 : p ∣ b ^ 3 := dvd_trans hp_dvd_b (dvd_pow_self b (by decide : 3 ≠ 0))
  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq h
  have hp_dvd_sub : p ∣ c ^ 3 - b ^ 3 := Nat.dvd_sub hp_dvd_c3 hp_dvd_b3
  have hp_dvd_a3 : p ∣ a ^ 3 := by simpa [hsub] using hp_dvd_sub
  have hp_dvd_a : p ∣ a := hp.dvd_of_dvd_pow hp_dvd_a3
  have hp_dvd_gab : p ∣ Nat.gcd a b := Nat.dvd_gcd hp_dvd_a hp_dvd_b
  have : p ∣ 1 := by simpa [hab.gcd_eq_one] using hp_dvd_gab
  exact hp.not_dvd_one this

lemma exists_prime_factor_cube_diff_of_three_dvd_sub {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) (h3 : 3 ∣ c - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ c ^ 3 - b ^ 3 ∧ ¬ q ∣ c - b := by
  rcases h3 with ⟨k, hk⟩
  have hdiff_pos : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hk_pos : 0 < k := by
    have : 0 < 3 * k := by simpa [hk] using hdiff_pos
    exact Nat.pos_of_mul_pos_left this
  have hc_eq : c = 3 * k + b := by
    calc
      c = (c - b) + b := (Nat.sub_add_cancel hbc.le).symm
      _ = 3 * k + b := by simp only [hk]
  let m : ℕ := 3 * k ^ 2 + 3 * k * b + b ^ 2
  have hm_gt1 : 1 < m := by
    have hk2_pos : 0 < k ^ 2 := by positivity
    have hb2_pos : 0 < b ^ 2 := by positivity
    dsimp [m]
    omega
  obtain ⟨q, hq, hq_dvd_m⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hm_gt1)
  have h3_ndvd_b : ¬ 3 ∣ b := by
    intro h3b
    have h3c : 3 ∣ c := by
      have : 3 ∣ (c - b) + b := dvd_add (by exact ⟨k, hk⟩) h3b
      simpa [Nat.sub_add_cancel hbc.le] using this
    have h3gcd : 3 ∣ Nat.gcd c b := Nat.dvd_gcd h3c h3b
    have h3one : 3 ∣ 1 := by
      simp only [hcop.gcd_eq_one, Nat.dvd_one, OfNat.ofNat_ne_one] at h3gcd
    exact Nat.prime_three.not_dvd_one h3one
  have h3_ndvd_m : ¬ 3 ∣ m := by
    intro h3m
    have h3_dvd_t1 : 3 ∣ 3 * k ^ 2 := by
      simp only [dvd_mul_right]
    have h3_dvd_t2 : 3 ∣ 3 * k * b := by
      have : 3 ∣ 3 * k := by
        simp only [dvd_mul_right]
      exact dvd_mul_of_dvd_left this b
    have h3_dvd_sum12 : 3 ∣ 3 * k ^ 2 + 3 * k * b := dvd_add h3_dvd_t1 h3_dvd_t2
    have hm_eq : m = (3 * k ^ 2 + 3 * k * b) + b ^ 2 := by
      rfl
    have h3_dvd_b2 : 3 ∣ b ^ 2 := by
      exact (Nat.dvd_add_right h3_dvd_sum12).1 (by simpa [hm_eq] using h3m)
    have h3b : 3 ∣ b := Nat.prime_three.dvd_of_dvd_pow h3_dvd_b2
    exact h3_ndvd_b h3b
  have hq_ndvd_three : ¬ q ∣ 3 := by
    intro hq3
    have hq_eq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hq3
    exact h3_ndvd_m (hq_eq3 ▸ hq_dvd_m)
  have hq_ndvd_k : ¬ q ∣ k := by
    intro hqk
    have hm_eq : m = k * (3 * k + 3 * b) + b ^ 2 := by
      dsimp [m]
      ring
    have hq_dvd_prod : q ∣ k * (3 * k + 3 * b) := dvd_mul_of_dvd_left hqk _
    have hq_dvd_b2 : q ∣ b ^ 2 := by
      exact (Nat.dvd_add_right hq_dvd_prod).1 (by simpa [hm_eq] using hq_dvd_m)
    have hq_dvd_b : q ∣ b := hq.dvd_of_dvd_pow hq_dvd_b2
    have hq_dvd_c : q ∣ c := by
      have hq_dvd_3k : q ∣ 3 * k := dvd_mul_of_dvd_right hqk 3
      have : q ∣ 3 * k + b := dvd_add hq_dvd_3k hq_dvd_b
      simpa [hc_eq] using this
    have : q ∣ Nat.gcd c b := Nat.dvd_gcd hq_dvd_c hq_dvd_b
    have : q ∣ 1 := by simpa [hcop.gcd_eq_one] using this
    exact hq.not_dvd_one this
  have hq_ndvd_diff : ¬ q ∣ c - b := by
    intro hqd
    have hq_dvd_3k : q ∣ 3 * k := by simpa [hk] using hqd
    rcases hq.dvd_mul.mp hq_dvd_3k with hq3 | hqk
    · exact hq_ndvd_three hq3
    · exact hq_ndvd_k hqk
  have hS0 : S0_nat c b = 3 * m := by
    unfold S0_nat
    dsimp [m]
    rw [hc_eq]
    ring
  have hq_dvd_S0 : q ∣ S0_nat c b := by
    have : q ∣ 3 * m := dvd_mul_of_dvd_right hq_dvd_m 3
    simpa [hS0] using this
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
    simpa [S0_nat] using hdiff
  have hq_dvd_diff : q ∣ c ^ 3 - b ^ 3 := by
    rw [hfact]
    exact dvd_mul_of_dvd_right hq_dvd_S0 (c - b)
  exact ⟨q, hq, hq_dvd_diff, hq_ndvd_diff⟩

lemma quotientPrimePow_gt_one {a b p : ℕ}
    (hp : Nat.Prime p) (ha : b < a) (_hb : 0 < b) :
    1 < quotientPrimePow a b p := by
  have hab_pos : 0 < a - b := Nat.sub_pos_of_lt ha
  have hab_ne : a - b ≠ 0 := Nat.ne_of_gt hab_pos
  -- p ≥ 2
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hp1_pos : 0 < p - 1 := by
    -- 1 < p (prime) なので p-1 > 0
    exact Nat.sub_pos_of_lt hp.one_lt
  -- 1 < a（a > b ≥ 0 かつ b < a より、a ≥ 1 では弱いので、ここは 1 < a を作る）
  have ha_gt1 : 1 < a := by
    -- b < a かつ b ≥ 0 なので a ≥ 1、さらに a ≠ 1 を言えば 1 < a
    -- ここは簡単に omega が通るなら omega、通らなければ場合分けでもOK
    omega
  -- 2 ≤ a^(p-1)
  have two_le_apow : 2 ≤ a^(p-1) := by
    -- 2 ≤ m ↔ 1 < m
    have : 1 < a^(p-1) := by
      calc 1
        _ = a^0 := (pow_zero a).symm
        _ < a^(p-1) := Nat.pow_lt_pow_right ha_gt1 hp1_pos
    exact Nat.succ_le_of_lt this
  -- a^(p-1) ≤ (a^p - b^p) / (a-b)
  have apow_le_quot : a^(p-1) ≤ quotientPrimePow a b p := by
    unfold quotientPrimePow
    -- Nat.le_div_iff_mul_le : 0 < k → (m ≤ n / k ↔ m*k ≤ n)
    have hmul : a^(p-1) * (a - b) ≤ a^p - b^p := by
      -- b^p ≤ a^(p-1)*b を示して引き算で吸収
      have hb_le_a : b ≤ a := Nat.le_of_lt ha
      have hbpow_le_apow : b^(p-1) ≤ a^(p-1) := Nat.pow_le_pow_left hb_le_a (p-1)
      have hb_mul : b^(p-1) * b ≤ a^(p-1) * b := Nat.mul_le_mul_right b hbpow_le_apow
      have hbpow : b^p = b^(p-1) * b := by
        -- p = (p-1)+1
        have hp_eq : p = (p - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.2 hp.pos)).symm
        -- b^p = b^(p-1+1) = b^(p-1) * b
        rw [hp_eq]
        exact pow_succ b (p - 1)
      have hapow : a^p = a^(p-1) * a := by
        have hp_eq : p = (p - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.2 hp.pos)).symm
        rw [hp_eq]
        exact pow_succ a (p - 1)
      -- 目的：a^(p-1)*(a-b) ≤ a^p - b^p
      --     ⇔ a^(p-1)*a - a^(p-1)*b ≤ a^p - b^p
      --     ⇔ b^p ≤ a^(p-1)*b
      -- そして b^p = b^(p-1)*b ≤ a^(p-1)*b
      have hbpow_le : b^p ≤ a^(p-1) * b := by
        rw [hbpow]
        exact hb_mul
      have hab_pow_le : b^p ≤ a^p := Nat.pow_le_pow_left hb_le_a p
      have ha_ge_b_pow : a^(p-1) * b ≤ a^p := by
        calc a^(p-1) * b
          _ ≤ a^(p-1) * a := Nat.mul_le_mul_left _ hb_le_a
          _ = a^p := by rw [← hapow]
      calc a^(p-1) * (a - b)
        _ = a^(p-1) * a - a^(p-1) * b := Nat.mul_sub_left_distrib (a^(p-1)) a b
        _ = a^p - a^(p-1) * b := by rw [← hapow]
        _ ≤ a^p - b^p := Nat.sub_le_sub_left hbpow_le (a^p)
    exact (Nat.le_div_iff_mul_le hab_pos).2 hmul
  -- 2 ≤ quotient → 1 < quotient
  have : 2 ≤ quotientPrimePow a b p := le_trans two_le_apow apow_le_quot
  exact Nat.lt_of_succ_le this

theorem pow_sub_pow_factor {α : Type*} [CommRing α] (a b : α) (d : ℕ) :
    a^d - b^d = (a - b) * diffPowSum a b d := by
  induction d with
  | zero =>
    simp [diffPowSum, Finset.range_zero, Finset.sum_empty]
  | succ d ih =>
    have eq1 : a^(d + 1) - b^(d + 1) = a * a^d - b * b^d := by ring
    rw [eq1]
    have eq2 : a * a^d - b * b^d = (a - b) * a^d + b * (a^d - b^d) := by ring
    rw [eq2, ih]
    have : diffPowSum a b (d + 1) = a^d + b * diffPowSum a b d := by
      unfold diffPowSum
      -- split the 0-th term and shift the rest (use sum_range_succ' to get f 0 + ∑ f (i+1))
      rw [Finset.sum_range_succ']
      -- show the tail sum equals b * the shifted sum
      have tail_eq : ∑ k ∈ Finset.range d, a ^ (d + 1 - 1 - (k + 1)) * b ^ (k + 1) =
                     b * ∑ i ∈ Finset.range d, a ^ (d - 1 - i) * b ^ i := by
        -- move the `b` inside the sum so `sum_congr` can match summands
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [add_tsub_cancel_right, pow_succ, Nat.sub_sub, Nat.add_comm]; ring
      rw [tail_eq]
      grind
    rw [this]
    grind

lemma pow_sub_pow_eq_diff_mul_quotient {a b p : ℕ}
    (_hp : Nat.Prime p) (ha : b < a) :
    a^p - b^p = (a - b) * quotientPrimePow a b p := by
  unfold quotientPrimePow
  -- ℤ での pow_sub_pow_factor を使う
  have key : (a : ℤ)^p - (b : ℤ)^p = ((a : ℤ) - (b : ℤ)) * diffPowSum (a : ℤ) (b : ℤ) p :=
    pow_sub_pow_factor (a : ℤ) (b : ℤ) p
  -- Nat での可除性に変換
  have hab_le : b ≤ a := Nat.le_of_lt ha
  have hab_pow : b^p ≤ a^p := Nat.pow_le_pow_left hab_le p
  -- (a - b) ∣ (a^p - b^p) を Int から示す
  have hdvd : (a - b) ∣ (a^p - b^p) := by
    have h1 : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) := Nat.cast_sub hab_le
    have h2 : ((a^p - b^p : ℕ) : ℤ) = (a : ℤ)^p - (b : ℤ)^p := by
      simp only [Nat.cast_sub hab_pow, Nat.cast_pow]
    have key' : (a : ℤ) - (b : ℤ) ∣ (a : ℤ)^p - (b : ℤ)^p := by
      rw [key]
      exact dvd_mul_right _ _
    rw [← h1, ← h2] at key'
    exact Int.ofNat_dvd.mp key'
  -- div_mul_cancel を使う
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel hdvd).symm

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
    change (∑ i ∈ Finset.range d, a ^ (d - 1 - i) * b ^ i) - (d : ℤ) * b ^ (d - 1)
      = ∑ i ∈ Finset.range d, (a ^ (d - 1 - i) * b ^ i - b ^ (d - 1))
    have : (d : ℤ) * b ^ (d - 1) = ∑ i ∈ Finset.range d, b ^ (d - 1) := by
      simp [Finset.sum_const, Finset.card_range]
    rw [this]
    simp only [Finset.sum_sub_distrib]
  -- each term a^(m) - b^(m) is divisible by a - b
  have term_div : ∀ i ∈ Finset.range d, (a - b) ∣ (a ^ (d - 1 - i) - b ^ (d - 1 - i)) := by
    intro i hi
    have eq := pow_sub_pow_factor (a := a) (b := b) (d := d - 1 - i)
    rw [eq]
    simp only [dvd_mul_right]
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
      have eq : (d - 1) = (d - 1 - i) + i := by grind  -- omega -- ok
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
      -- derive contradiction pp ∣ b
      have : b = pp * bm := by rw [h1, h2]
      have pp_div_b : pp ∣ b := by use bm
      have : False := pp_not_dvd_b pp_div_b
      contradiction -- finish ok
  -- done: (p : ℕ) ∣ d
  exact this

lemma exists_prime_divisor_not_dividing_diff_of_prime_exp
    {a b p : ℕ}
    (hp : Nat.Prime p) (_hp_ge : 3 ≤ p)
    (ha : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ p ∣ a - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^p - b^p ∧ ¬ q ∣ a - b := by
  -- 方針：G = (a^p - b^p) / (a - b) の素因子を取る
  have hG_gt : 1 < quotientPrimePow a b p := quotientPrimePow_gt_one hp ha hb
  have hG_ne : quotientPrimePow a b p ≠ 1 := Nat.ne_of_gt hG_gt
  -- G ≠ 1 なので素因子が存在
  have ⟨q, hq_prime, hq_div_G⟩ := Nat.exists_prime_and_dvd hG_ne
  use q, hq_prime
  constructor
  · -- q ∣ G かつ a^p - b^p = (a-b) * G なので q ∣ a^p - b^p
    have heq := pow_sub_pow_eq_diff_mul_quotient hp ha
    rw [heq]
    exact dvd_mul_of_dvd_right hq_div_G _
  · -- q ∣ a - b なら矛盾を導く
    intro hq_div_diff
    -- 戦略: q | (a-b) かつ q | quotientPrimePow から q | p を導き、q = p となるが、
    -- これは hpnd : ¬ p ∣ a - b と矛盾する

    -- まず Nat.Coprime を Int.gcd に変換
    have hab_int : Int.gcd (a : ℤ) (b : ℤ) = 1 := by
      simp only [Int.gcd_eq_natAbs]
      have : Nat.gcd a b = 1 := hab
      simp [this]
    -- (a-b) * quotientPrimePow a b p = a^p - b^p
    have heq_mul : (a - b) * quotientPrimePow a b p = a^p - b^p :=
      (pow_sub_pow_eq_diff_mul_quotient hp ha).symm
    -- a^p - b^p = (a-b) * diffPowSum a b p (ℤ)
    have key_int : (a : ℤ)^p - (b : ℤ)^p = ((a : ℤ) - (b : ℤ)) * diffPowSum (a : ℤ) (b : ℤ) p :=
      pow_sub_pow_factor (a : ℤ) (b : ℤ) p
    -- quotientPrimePow a b p と diffPowSum (a : ℤ) (b : ℤ) p の関係を導く
    have hab_le : b ≤ a := Nat.le_of_lt ha
    have hab_pow : b^p ≤ a^p := Nat.pow_le_pow_left hab_le p
    have quot_eq_sum : (quotientPrimePow a b p : ℤ) = diffPowSum (a : ℤ) (b : ℤ) p := by
      have h1 : ((a^p - b^p : ℕ) : ℤ) = (a : ℤ)^p - (b : ℤ)^p := by
        simp only [Nat.cast_sub hab_pow, Nat.cast_pow]
      have h2 : (↑(a - b) : ℤ) = (a : ℤ) - (b : ℤ) := by omega
      have heq_cast : (↑((a - b) * quotientPrimePow a b p) : ℤ) = ↑(a^p - b^p) := by
        rw [heq_mul]
      simp only [Nat.cast_mul] at heq_cast
      rw [h1, h2] at heq_cast
      rw [key_int] at heq_cast
      -- ((a : ℤ) - (b : ℤ)) * ↑(quotientPrimePow a b p) = ((a : ℤ) - (b : ℤ)) * diffPowSum ...
      have hab_ne_zero : (a : ℤ) - (b : ℤ) ≠ 0 := by omega
      exact (mul_right_inj' hab_ne_zero).mp heq_cast
    -- q ∣ quotientPrimePow より q ∣ diffPowSum (ℤ)
    have q_div_sum : (q : ℤ) ∣ diffPowSum (a : ℤ) (b : ℤ) p := by
      rw [← quot_eq_sum]
      exact Int.ofNat_dvd.mpr hq_div_G
    -- q ∣ a - b (ℤ)
    have q_div_diff_int : (q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := by
      have : (a : ℤ) - (b : ℤ) = ↑(a - b) := by omega
      rw [this]
      exact Int.ofNat_dvd.mpr hq_div_diff
    -- q  gcd(a-b, diffPowSum) を導く
    have hgcd_div : (q : ℤ) ∣ ↑(Int.gcd ((a : ℤ) - (b : ℤ)) (diffPowSum (a : ℤ) (b : ℤ) p)) := by
      -- より簡潔な証明：q | x かつ q | y ならば q | gcd(x,y)
      apply Int.ofNat_dvd.mpr
      apply Nat.dvd_gcd
      · -- q ∣ (a - b).natAbs を示す
        have : ((a : ℤ) - (b : ℤ)).natAbs = a - b := by
          have heq : (a : ℤ) - (b : ℤ) = ↑(a - b) := by omega
          simp [heq]
        rw [this]
        exact hq_div_diff
      · -- q ∣ (diffPowSum ...).natAbs を示す
        -- diffPowSum (a : ℤ) (b : ℤ) p = quotientPrimePow a b p (as ℤ)
        have : diffPowSum (a : ℤ) (b : ℤ) p = (quotientPrimePow a b p : ℤ) := quot_eq_sum.symm
        rw [this]
        have : ((quotientPrimePow a b p : ℤ)).natAbs = quotientPrimePow a b p := by
          norm_cast
        rw [this]
        exact hq_div_G
    -- prime_dividing_gcd_divides_d より q ∣ p
    have hq_div_p : (q : ℕ) ∣ p := by
      exact prime_dividing_gcd_divides_d hq_prime hab_int hgcd_div
    -- q, p はどちらも素数で q ∣ p なので q = p
    have hq_eq_p : q = p := by
      have := hp.eq_one_or_self_of_dvd q hq_div_p
      rcases this with h1 | h2
      · exact absurd h1 hq_prime.ne_one
      · exact h2
    -- しかし hpnd : ¬ p ∣ a - b と hq_div_diff : q ∣ a - b および q = p から矛盾
    rw [hq_eq_p] at hq_div_diff
    exact hpnd hq_div_diff

lemma exists_primitive_prime_factor_basic {a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  -- GcdDiffPow の補題を直接使う
  exact exists_prime_divisor_not_dividing_diff_of_prime_exp hd_prime hd_ge hab_lt hb hab hpnd

lemma exists_primitive_prime_factor_prime {a b : ℕ} {d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  exact exists_primitive_prime_factor_basic hd_prime hd_ge hab_lt hb hab hpnd

lemma exists_prime_factor_cube_diff_of_not_three_dvd_sub {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ c ^ 3 - b ^ 3 ∧ ¬ q ∣ c - b := by
  exact exists_primitive_prime_factor_prime
    Nat.prime_three (by norm_num : 3 ≤ 3) hbc hb hcop h3

lemma exists_prime_factor_cube_diff {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ c ^ 3 - b ^ 3 ∧ ¬ q ∣ c - b := by
  by_cases h3 : 3 ∣ c - b
  · exact exists_prime_factor_cube_diff_of_three_dvd_sub hbc hb hcop h3
  · exact exists_prime_factor_cube_diff_of_not_three_dvd_sub hbc hb hcop h3

lemma padicValNat_lower_bound_of_dvd_d3 {c q : ℕ}
    (hc_pos : 0 < c)
    (hq : Nat.Prime q)
    (hq_dvd_c : q ∣ c) :
    3 ≤ padicValNat q (c ^ 3) := by
  have h_c_ne : c ≠ 0 := Nat.ne_of_gt hc_pos
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h_val_c_ge_1 : 1 ≤ padicValNat q c := by
    have h_ne_zero : padicValNat q c ≠ 0 := by
      intro h
      have : ¬ q ∣ c := by
        rcases padicValNat.eq_zero_iff.mp h with hq1 | hc0 | hqndvd
        · exact (hq.ne_one hq1).elim
        · exact (h_c_ne hc0).elim
        · exact hqndvd
      exact this hq_dvd_c
    omega
  have h_val_pow : padicValNat q (c ^ 3) = 3 * padicValNat q c :=
    padicValNat.pow (n := 3) h_c_ne
  rw [h_val_pow]
  omega

@[simp] def GN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R :=
    ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k)

theorem cosmic_id_csr' {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
        (x + u) ^ d = x * GN d x u + u ^ d := by
    unfold GN
    rw [add_pow, Finset.mul_sum]
    -- 二項展開を k=0 項と k≥1 項に分ける（項の順序を `add_pow` の出力に合わせる）
    have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * (Nat.choose d k : R)
        = x ^ 0 * u ^ d * (Nat.choose d 0 : R)
            + ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.sub_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have hk' : k < d := Finset.mem_range.mp hk
        have hss : k + 1 ≤ d := Nat.succ_le_of_lt hk'
        have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
        have h3 : d - k - 1 = d - 1 - k := by omega
        rw [h2, h3]
    -- x * G を展開すると h1 の第2項と一致する（項順序を合わせる）
    have h2 : ∑ k ∈ Finset.range d, x * ((Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k))
        = ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    -- 以上の等式から二項展開の和が x*G + u^d に一致する
    rw [h1, h2]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    ring

lemma sub_eq_mul_GN (d x u : ℕ) :
    (x + u) ^ d - u ^ d = x * GN d x u := by
  have hbig : (x + u) ^ d = x * GN d x u + u ^ d := cosmic_id_csr' d x u
  have hpow : u ^ d ≤ (x + u) ^ d := by
    exact Nat.pow_le_pow_left (Nat.le_add_left u x) d
  omega

lemma prime_dvd_GN_of_dvd_sub_not_dvd_left {d x u q : ℕ}
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ (x + u) ^ d - u ^ d)
    (hq_ndvd : ¬ q ∣ x) :
    q ∣ GN d x u := by
  have hmul : q ∣ x * GN d x u := by
    simpa [sub_eq_mul_GN d x u] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

lemma GN_three_explicit (x u : ℕ) :
    GN 3 x u = x ^ 2 + 3 * x * u + 3 * u ^ 2 := by
  apply Int.subNat_eq_zero_iff.mp
  -- G 3 x u - (x^2 + 3xu + 3u^2) = 0 を示す
  unfold GN
  -- 計算を進める
  have h1 : Nat.choose 3 1 = 3 := by norm_num
  have h2 : Nat.choose 3 2 = 3 := by norm_num
  have h3 : Nat.choose 3 3 = 1 := by norm_num
  -- Finset.range をシンプルにするため、具体的に展開
  simp [Finset.range_add_one]
  ring

lemma GN_three_sub_eq_S0_nat {c b : ℕ} (hbc : b < c) :
    GN 3 (c - b) b = S0_nat c b := by
  rw [GN_three_explicit (c - b) b]
  unfold S0_nat
  zify [hbc]
  ring_nf

lemma prime_dvd_S0_via_cosmic_bridge {c b q : ℕ}
    (hbc : b < c)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
    (hq_ndvd : ¬ q ∣ c - b) :
    q ∣ S0_nat c b := by
  have hq_dvd_sub : q ∣ ((c - b) + b) ^ 3 - b ^ 3 := by
    simpa [Nat.sub_add_cancel hbc.le] using hq_dvd
  have hq_dvd_GN_raw : q ∣ GN 3 (c - b) b := by
    exact prime_dvd_GN_of_dvd_sub_not_dvd_left
      (d := 3) hq hq_dvd_sub hq_ndvd
  have hq_dvd_GN : q ∣ GN 3 (c - b) b := by
    change q ∣
      (∑ x ∈ Finset.range 3,
        Nat.choose 3 (x + 1) * (c - b) ^ x * b ^ (2 - x)) at hq_dvd_GN_raw
    simpa [GN] using hq_dvd_GN_raw
  have hGN_eq : GN 3 (c - b) b = S0_nat c b := GN_three_sub_eq_S0_nat hbc
  rw [hGN_eq] at hq_dvd_GN
  exact hq_dvd_GN

lemma cube_sub_eq_mul_sub_S0 {c b : ℕ} (hbc : b < c) :
    c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  simpa [S0_nat] using hdiff

lemma padicValNat_le_one_of_not_sq_dvd (a b q : ℕ)
    (_ha : 0 < a) (_hb : 0 < b)
    (hq : Nat.Prime q)
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b) :
    padicValNat q (S0_nat a b) ≤ 1 := by
  -- q | S0 より padicValNat q (S0) ≥ 1
  -- q² ∤ S0 より padicValNat q (S0) ≤ 1
  -- したがって padicValNat q (S0) ≤ 1
  haveI hp : Fact q.Prime := ⟨hq⟩
  have h_S0_ne : S0_nat a b ≠ 0 := by
    unfold S0_nat
    intro h
    have : a^2 + a*b + b^2 = 0 := h
    have : 0 < a^2 := by positivity
    omega
  by_contra h
  push_neg at h
  have : q^2 ∣ S0_nat a b := by
    rw [padicValNat_dvd_iff 2 (S0_nat a b)]
    right
    exact h
  exact hq_not_sq this

lemma padicValNat_upper_bound_d3 {a b q : ℕ}
    (hab_lt : b < a)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ a ^ 3 - b ^ 3)
    (hq_ndiv_diff : ¬ q ∣ a - b)
    (hq_not_sq : ¬ q ^ 2 ∣ S0_nat a b) :
    padicValNat q (a ^ 3 - b ^ 3) ≤ 1 := by
  have hS0_dvd : q ∣ S0_nat a b :=
    prime_dvd_S0_via_cosmic_bridge hab_lt hq hq_dvd hq_ndiv_diff
  have h_fact : a ^ 3 - b ^ 3 = (a - b) * S0_nat a b :=
    cube_sub_eq_mul_sub_S0 hab_lt
  have hpadic_bound : padicValNat q (S0_nat a b) ≤ 1 :=
    padicValNat_le_one_of_not_sq_dvd a b q ha_pos hb_pos hq hq_not_sq
  have ha_minus_b_ne_zero : a - b ≠ 0 := Nat.sub_ne_zero_of_lt hab_lt
  have hS0_ne_zero : S0_nat a b ≠ 0 := by
    unfold S0_nat
    have ha2_pos : 0 < a ^ 2 := by positivity
    have hab_pos : 0 < a * b := by positivity
    have hb2_pos : 0 < b ^ 2 := by positivity
    omega
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h_val_diff_zero : padicValNat q (a - b) = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_ndiv_diff
  have h_val_mult : padicValNat q (a ^ 3 - b ^ 3) =
      padicValNat q (a - b) + padicValNat q (S0_nat a b) :=
    congrArg (padicValNat q) h_fact ▸ padicValNat.mul ha_minus_b_ne_zero hS0_ne_zero
  calc padicValNat q (a ^ 3 - b ^ 3)
      = padicValNat q (a - b) + padicValNat q (S0_nat a b) := h_val_mult
    _ = padicValNat q (S0_nat a b) := by simp [h_val_diff_zero]
    _ ≤ 1 := hpadic_bound

theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro h_eq
  have hcop_cb : Nat.Coprime c b := coprime_cb_of_eq hab h_eq
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hc3_le : c ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hcb 3
    have hsum_le : a ^ 3 + b ^ 3 ≤ b ^ 3 := by simpa [h_eq] using hc3_le
    have ha3_pos : 0 < a ^ 3 := by positivity
    omega
  obtain ⟨q, hq_prime, hq_dvd_diff, hq_ndiv_diff⟩ :=
    exists_prime_factor_cube_diff hbc hb hcop_cb
  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq h_eq
  have hq_dvd_a3 : q ∣ a ^ 3 := by simpa [hsub] using hq_dvd_diff
  have hq_dvd_a : q ∣ a := hq_prime.dvd_of_dvd_pow hq_dvd_a3
  have h_lower_a3 : 3 ≤ padicValNat q (a ^ 3) :=
    padicValNat_lower_bound_of_dvd_d3 ha hq_prime hq_dvd_a
  have h_lower : 3 ≤ padicValNat q (c ^ 3 - b ^ 3) := by
    simpa [hsub] using h_lower_a3
  have h_upper : padicValNat q (c ^ 3 - b ^ 3) ≤ 1 :=
    padicValNat_upper_bound_d3 hbc hc hb hq_prime hq_dvd_diff hq_ndiv_diff
      (hS0_not_sq hq_prime hq_dvd_diff hq_ndiv_diff)
  have : (3 : ℕ) ≤ 1 := le_trans h_lower h_upper
  omega

#print axioms FLT_d3_by_padicValNat  -- OK: 2026/02/25  0:35
-- 'FLT_d3_by_padicValNat' depends on axioms: [propext, Classical.choice, Quot.sound]

def NoSqOnS0 (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ^ 2 ∣ S0_nat c b

lemma hS0_not_sq_of_NoSqOnS0 {c b : ℕ}
    (hNoSq : NoSqOnS0 c b) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b := by
  intro q hq hq_dvd hq_ndvd
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hdiff_zero : c - b = 0 := Nat.sub_eq_zero_of_le hcb
    exact hq_ndvd (hdiff_zero ▸ dvd_zero q)
  have hqS0 : q ∣ S0_nat c b :=
    prime_dvd_S0_via_cosmic_bridge hbc hq hq_dvd hq_ndvd
  exact hNoSq hq hqS0

theorem FLT_d3_by_padicValNat_of_NoSqOnS0 {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hNoSq : NoSqOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  apply FLT_d3_by_padicValNat ha hb hc hab
  intro q hq hq_dvd_diff hq_ndiv_diff
  exact hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff

#print axioms FLT_d3_by_padicValNat_of_NoSqOnS0  -- OK: 2026/02/25  1:27
-- 'FLT_d3_by_padicValNat_of_NoSqOnS0' depends on axioms: [propext, Classical.choice, Quot.sound]

abbrev PeriodIndex := ℕ

structure NP where
  n : ℤ
  p : Bool
deriving DecidableEq, Repr

structure PetalCoreUnit where
  base : NP
deriving DecidableEq, Repr

def succ : NP → NP
  | ⟨n, false⟩ => ⟨n, true⟩
  | ⟨n, true⟩  => ⟨n + 1, false⟩

def coreSucc (u : PetalCoreUnit) : PetalCoreUnit :=
  ⟨succ u.base⟩

def HarmonicPoint (u : PetalCoreUnit) : Prop :=
  ∃ k : PeriodIndex, 0 < k ∧ (Nat.iterate coreSucc (2 * k) u).base.p = u.base.p

def isExceptionalPhase (u : PetalCoreUnit) : Prop :=
  u.base.p = true

def PrimitiveOnS0 (c b q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b

def NonLiftableS0 (c b q : ℕ) : Prop :=
  PrimitiveOnS0 c b q → ¬ q ^ 2 ∣ S0_nat c b

def AllNonLiftableOnS0 (c b : ℕ) : Prop :=
  (∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ∣ c - b)
    ∧ ∀ q : ℕ, NonLiftableS0 c b q

def NonExceptionalHarmonicOnS0 (c b : ℕ) : Prop :=
  (∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u) ∧ AllNonLiftableOnS0 c b

lemma AllNonLiftableOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : AllNonLiftableOnS0 c b := by
  exact h.2

lemma NoSqOnS0_of_AllNonLiftableOnS0 {c b : ℕ}
    (hAll : AllNonLiftableOnS0 c b) : NoSqOnS0 c b := by
  intro q hq hqS0
  rcases hAll with ⟨hprimSupport, hnonlift⟩
  have hq_ndvd : ¬ q ∣ c - b := hprimSupport hq hqS0
  have hprim : PrimitiveOnS0 c b q := ⟨hq, hqS0, hq_ndvd⟩
  exact hnonlift q hprim

theorem FLT_d3_by_padicValNat_of_nonExceptionalHarmonic {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hNH : NonExceptionalHarmonicOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hAll : AllNonLiftableOnS0 c b :=
    AllNonLiftableOnS0_of_nonExceptionalHarmonic hNH
  have hNoSq : NoSqOnS0 c b := NoSqOnS0_of_AllNonLiftableOnS0 hAll
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab
    hNoSq

#print axioms FLT_d3_by_padicValNat_of_nonExceptionalHarmonic  -- OK: 2026/02/25  1:26
-- 'FLT_d3_by_padicValNat_of_nonExceptionalHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound]

def S0PrimeSupportExceptThree (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → q ≠ 3 → ¬ q ∣ c - b

lemma NoSqOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : NoSqOnS0 c b := by
  exact NoSqOnS0_of_AllNonLiftableOnS0 (AllNonLiftableOnS0_of_nonExceptionalHarmonic h)

lemma not_three_dvd_S0_of_mod3_separated {c b : ℕ}
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    ¬ 3 ∣ S0_nat c b := by
  have hc_lt : c % 3 < 3 := Nat.mod_lt _ (by decide)
  have hb_lt : b % 3 < 3 := Nat.mod_lt _ (by decide)
  have hc_cases : c % 3 = 1 ∨ c % 3 = 2 := by omega
  have hb_cases : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hc_cases with hc1 | hc2
  · rcases hb_cases with hb1 | hb2
    · exfalso
      exact hsep (by simp [hc1, hb1])
    · intro h3S0
      have hc_mod1 : c ≡ 1 [MOD 3] := by simpa [Nat.ModEq] using hc1
      have hb_mod2 : b ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hb2
      have hS0_mod_const : S0_nat c b ≡ (1 ^ 2 + 1 * 2 + 2 ^ 2) [MOD 3] := by
        unfold S0_nat
        exact ((hc_mod1.pow 2).add (hc_mod1.mul hb_mod2)).add (hb_mod2.pow 2)
      have hconst : ((1 ^ 2 + 1 * 2 + 2 ^ 2 : ℕ) ≡ 1 [MOD 3]) := by decide
      have hS0_mod1 : S0_nat c b ≡ 1 [MOD 3] := hS0_mod_const.trans hconst
      have hS0_mod0 : S0_nat c b ≡ 0 [MOD 3] := h3S0.modEq_zero_nat
      have h10 : (1 : ℕ) ≡ 0 [MOD 3] := hS0_mod1.symm.trans hS0_mod0
      norm_num [Nat.ModEq] at h10
  · rcases hb_cases with hb1 | hb2
    · intro h3S0
      have hc_mod2 : c ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hc2
      have hb_mod1 : b ≡ 1 [MOD 3] := by simpa [Nat.ModEq] using hb1
      have hS0_mod_const : S0_nat c b ≡ (2 ^ 2 + 2 * 1 + 1 ^ 2) [MOD 3] := by
        unfold S0_nat
        exact ((hc_mod2.pow 2).add (hc_mod2.mul hb_mod1)).add (hb_mod1.pow 2)
      have hconst : ((2 ^ 2 + 2 * 1 + 1 ^ 2 : ℕ) ≡ 1 [MOD 3]) := by decide
      have hS0_mod1 : S0_nat c b ≡ 1 [MOD 3] := hS0_mod_const.trans hconst
      have hS0_mod0 : S0_nat c b ≡ 0 [MOD 3] := h3S0.modEq_zero_nat
      have h10 : (1 : ℕ) ≡ 0 [MOD 3] := hS0_mod1.symm.trans hS0_mod0
      norm_num [Nat.ModEq] at h10
    · exfalso
      exact hsep (by simp [hc2, hb2])

def AllNonLiftableOnS0ExceptThree (c b : ℕ) : Prop :=
  S0PrimeSupportExceptThree c b ∧ (∀ q : ℕ, NonLiftableS0 c b q) ∧ ¬ 3 ∣ S0_nat c b

lemma allPrimeSupport_of_exceptThree {c b : ℕ}
    (hSupp : S0PrimeSupportExceptThree c b)
    (h3free : ¬ 3 ∣ S0_nat c b) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ∣ c - b := by
  intro q hq hqS0
  by_cases hq3 : q = 3
  · intro hqdiff
    have h3S0 : 3 ∣ S0_nat c b := by simpa [hq3] using hqS0
    exact h3free h3S0
  · exact hSupp hq hqS0 hq3

lemma AllNonLiftableOnS0_of_exceptThree {c b : ℕ}
    (h : AllNonLiftableOnS0ExceptThree c b) : AllNonLiftableOnS0 c b := by
  rcases h with ⟨hSuppEx3, hNonLift, h3free⟩
  refine ⟨allPrimeSupport_of_exceptThree hSuppEx3 h3free, hNonLift⟩

lemma AllNonLiftableOnS0_of_exceptThree_mod3_separated {c b : ℕ}
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    AllNonLiftableOnS0 c b := by
  have h3free : ¬ 3 ∣ S0_nat c b :=
    not_three_dvd_S0_of_mod3_separated hc_nz hb_nz hsep
  exact AllNonLiftableOnS0_of_exceptThree ⟨hSuppEx3, hNonLift, h3free⟩

lemma nonExceptionalHarmonicOnS0_of_allNonLiftable {c b : ℕ}
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hAll : AllNonLiftableOnS0 c b) :
    NonExceptionalHarmonicOnS0 c b := by
  exact ⟨hHarm, hAll⟩

lemma nonExceptionalHarmonicOnS0_of_exceptThree_mod3_separated {c b : ℕ}
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    NonExceptionalHarmonicOnS0 c b := by
  have hAll : AllNonLiftableOnS0 c b :=
    AllNonLiftableOnS0_of_exceptThree_mod3_separated hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact nonExceptionalHarmonicOnS0_of_allNonLiftable hHarm hAll

lemma NoSqOnS0_of_exceptThree_mod3_separated_harmonic {c b : ℕ}
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_nonExceptionalHarmonic
    (nonExceptionalHarmonicOnS0_of_exceptThree_mod3_separated
      hHarm hSuppEx3 hNonLift hc_nz hb_nz hsep)

theorem FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_exceptThree_mod3_separated_harmonic
      hHarm hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

#print axioms FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic  -- OK: 2026/02/25  1:32
-- 'FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]

structure NoSqInput (c b : ℕ) where
  hbc : b < c
  hcb_coprime : Nat.Coprime c b
  hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u
  hNoSq : NoSqOnS0 c b
  hc_nz : c % 3 ≠ 0
  hb_nz : b % 3 ≠ 0
  hsep : c % 3 ≠ b % 3

lemma prime_not_dvd_sub_of_prime_dvd_S0_coprime_ne_three {c b q : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (hq : Nat.Prime q)
    (hqS0 : q ∣ S0_nat c b)
    (hq_ne3 : q ≠ 3) :
    ¬ q ∣ c - b := by
  intro hq_sub
  have hcb_mod : c ≡ b [MOD q] := by
    exact ((Nat.modEq_iff_dvd' hbc).2 hq_sub).symm
  have hS0_mod3b2 : S0_nat c b ≡ 3 * b ^ 2 [MOD q] := by
    have h1 : S0_nat c b ≡ b ^ 2 + b * b + b ^ 2 [MOD q] := by
      unfold S0_nat
      exact ((hcb_mod.pow 2).add (hcb_mod.mul Nat.ModEq.rfl)).add Nat.ModEq.rfl
    have h2 : b ^ 2 + b * b + b ^ 2 = 3 * b ^ 2 := by
      ring
    exact h2 ▸ h1
  have hS0_mod0 : S0_nat c b ≡ 0 [MOD q] := hqS0.modEq_zero_nat
  have h3b2_mod0 : 3 * b ^ 2 ≡ 0 [MOD q] := hS0_mod3b2.symm.trans hS0_mod0
  have hq_3b2 : q ∣ 3 * b ^ 2 := Nat.modEq_zero_iff_dvd.mp h3b2_mod0
  rcases hq.dvd_mul.mp hq_3b2 with hq_three | hq_b2
  · have hq_eq_three : q = 3 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hq_three
    exact hq_ne3 hq_eq_three
  · have hq_b : q ∣ b := hq.dvd_of_dvd_pow hq_b2
    have hb_mod0 : b ≡ 0 [MOD q] := hq_b.modEq_zero_nat
    have hc_mod0 : c ≡ 0 [MOD q] := hcb_mod.trans hb_mod0
    have hq_c : q ∣ c := Nat.modEq_zero_iff_dvd.mp hc_mod0
    have hq_gcd : q ∣ Nat.gcd c b := Nat.dvd_gcd hq_c hq_b
    have hq_one : q ∣ 1 := by simpa [hcop.gcd_eq_one] using hq_gcd
    exact hq.not_dvd_one hq_one

lemma s0PrimeSupportExceptThree_of_coprime {c b : ℕ}
    (hbc : b ≤ c) (hcop : Nat.Coprime c b) :
    S0PrimeSupportExceptThree c b := by
  intro q hq hqS0 hq_ne3
  exact prime_not_dvd_sub_of_prime_dvd_S0_coprime_ne_three hbc hcop hq hqS0 hq_ne3

lemma s0PrimeSupportExceptThree_of_NoSqInput {c b : ℕ}
    (h : NoSqInput c b) :
    S0PrimeSupportExceptThree c b := by
  exact s0PrimeSupportExceptThree_of_coprime h.hbc.le h.hcb_coprime

lemma nonLiftableS0_all_of_NoSqOnS0 {c b : ℕ}
    (hNoSq : NoSqOnS0 c b) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  intro q hprim
  exact hNoSq hprim.1 hprim.2.1

lemma not_NoSqOnS0_iff_exists_sq_factor {c b : ℕ} :
    ¬ NoSqOnS0 c b ↔
      ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b := by
  classical
  constructor
  · intro hNoSq
    by_contra hnone
    apply hNoSq
    intro q hq hqS0 hq2
    exact hnone ⟨q, hq, hqS0, hq2⟩
  · intro hsq hNoSq
    rcases hsq with ⟨q, hq, hqS0, hq2⟩
    exact (hNoSq hq hqS0) hq2

lemma exists_sq_factor_split_three {c b : ℕ}
    (hsq : ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b) :
    (3 ^ 2 ∣ S0_nat c b) ∨
      ∃ q : ℕ, Nat.Prime q ∧ q ≠ 3 ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b := by
  rcases hsq with ⟨q, hq, hqS0, hq2⟩
  by_cases hq3 : q = 3
  · left
    simpa [hq3] using hq2
  · right
    exact ⟨q, hq, hq3, hqS0, hq2⟩

lemma not_exists_sq_factor_ne_three_of_support_nonLiftable {c b : ℕ}
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q) :
    ¬ ∃ q : ℕ, Nat.Prime q ∧ q ≠ 3 ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b := by
  intro hne3
  rcases hne3 with ⟨q, hq, hq_ne3, hqS0, hq2⟩
  have hq_ndvd_diff : ¬ q ∣ c - b := hSuppEx3 hq hqS0 hq_ne3
  have hPrim : PrimitiveOnS0 c b q := ⟨hq, hqS0, hq_ndvd_diff⟩
  exact (hNonLift q hPrim) hq2

lemma three_sq_dvd_of_not_NoSqOnS0_of_support_nonLiftable {c b : ℕ}
    (hNoSq_false : ¬ NoSqOnS0 c b)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q) :
    3 ^ 2 ∣ S0_nat c b := by
  have hsq : ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b :=
    (not_NoSqOnS0_iff_exists_sq_factor).1 hNoSq_false
  rcases exists_sq_factor_split_three hsq with h3 | hne3
  · exact h3
  · exfalso
    exact (not_exists_sq_factor_ne_three_of_support_nonLiftable hSuppEx3 hNonLift) hne3

lemma three_sq_not_dvd_of_mod3_separated {c b : ℕ}
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    ¬ 3 ^ 2 ∣ S0_nat c b := by
  intro h9
  have h3S0 : 3 ∣ S0_nat c b := by
    exact dvd_trans (by decide : 3 ∣ 3 ^ 2) h9
  exact (not_three_dvd_S0_of_mod3_separated hc_nz hb_nz hsep) h3S0

lemma NoSqOnS0_of_support_nonLiftable_mod3_separated {c b : ℕ}
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    NoSqOnS0 c b := by
  by_contra hNoSq_false
  have h9 : 3 ^ 2 ∣ S0_nat c b :=
    three_sq_dvd_of_not_NoSqOnS0_of_support_nonLiftable hNoSq_false hSuppEx3 hNonLift
  exact (three_sq_not_dvd_of_mod3_separated hc_nz hb_nz hsep) h9

theorem FLT_d3_by_padicValNat_of_support_nonLiftable_mod3_separated {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_support_nonLiftable_mod3_separated
      hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

theorem FLT_d3_by_padicValNat_by_cases_NoSq {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  by_cases hNoSq : NoSqOnS0 c b
  · exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq
  · exact FLT_d3_by_padicValNat_of_support_nonLiftable_mod3_separated
      ha hb hc hab hSuppEx3 hNonLift hc_nz hb_nz hsep

theorem FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqInput {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hIn : NoSqInput c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hSuppEx3 : S0PrimeSupportExceptThree c b :=
    s0PrimeSupportExceptThree_of_NoSqInput hIn
  have hNonLift : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_all_of_NoSqOnS0 hIn.hNoSq
  exact FLT_d3_by_padicValNat_by_cases_NoSq
    ha hb hc hab hSuppEx3 hNonLift hIn.hc_nz hIn.hb_nz hIn.hsep

#print axioms FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqInput  -- OK: 2026/02/25  1:33
-- 'FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqInput' depends on axioms: [propext, Classical.choice, Quot.sound]
