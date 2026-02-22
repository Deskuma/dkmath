/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.Algebra.DiffPow

set_option linter.style.longLine false

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

set_option linter.unusedTactic false

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
        done
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
            done
      -- derive contradiction pp ∣ b
      have : b = pp * bm := by rw [h1, h2]
      have pp_div_b : pp ∣ b := by use bm
      have : False := pp_not_dvd_b pp_div_b
      contradiction -- finish ok
      done
  -- done: (p : ℕ) ∣ d
  exact this
  done


/-- a^p - b^p を a - b で割った商（p は素数） -/
def quotientPrimePow (a b p : ℕ) : ℕ :=
  (a^p - b^p) / (a - b)


/-- 素数冪の商 G が存在し、a^p - b^p = (a - b) * G -/
lemma pow_sub_pow_eq_diff_mul_quotient {a b p : ℕ}
    (_hp : Nat.Prime p) (ha : b < a) :
    a^p - b^p = (a - b) * quotientPrimePow a b p := by
  unfold quotientPrimePow
  -- ℤ での pow_sub_pow_factor を使う
  have key : (a : ℤ)^p - (b : ℤ)^p = ((a : ℤ) - (b : ℤ)) * diffPowSum (a : ℤ) (b : ℤ) p :=
    DkMath.Algebra.DiffPow.pow_sub_pow_factor (a : ℤ) (b : ℤ) p
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


/-- 素数冪の場合、商は正で 1 より大きい -/
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


/-- 素数冪の場合の軽量版 Zsigmondy（prime p, p ≥ 3）

**追加仮定**: `¬ p ∣ a - b` を入れることで、gcd 補題から完全な証明が可能になる。
-/
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
      DkMath.Algebra.DiffPow.pow_sub_pow_factor (a : ℤ) (b : ℤ) p
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
      exact DkMath.NumberTheory.GcdDiffPow.prime_dividing_gcd_divides_d hq_prime hab_int hgcd_div
    -- q, p はどちらも素数で q ∣ p なので q = p
    have hq_eq_p : q = p := by
      have := hp.eq_one_or_self_of_dvd q hq_div_p
      rcases this with h1 | h2
      · exact absurd h1 hq_prime.ne_one
      · exact h2
    -- しかし hpnd : ¬ p ∣ a - b と hq_div_diff : q ∣ a - b および q = p から矛盾
    rw [hq_eq_p] at hq_div_diff
    exact hpnd hq_div_diff

#print axioms exists_prime_divisor_not_dividing_diff_of_prime_exp  -- OK: 2026/02/22 23:20
-- 'DkMath.NumberTheory.GcdDiffPow.exists_prime_divisor_not_dividing_diff_of_prime_exp' depends on axioms: [propext, Classical.choice,  Quot.sound]

end DkMath.NumberTheory.GcdDiffPow
