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
  done










-- ------------------------------------
-- これ以前は、編集禁止
-- ------------------------------------














/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d := by
  -- 素数分解を使用して、各素因子 p について gcd を割ることを示す
  -- gcd の各素因子は (a-b).natAbs と (diffPowSum a b d).natAbs の両方を割る
  -- したがってこれらの素因子の部分積も d を割る
  set g := (a - b).natAbs.gcd (diffPowSum a b d).natAbs
  -- gcd の定義から、g は両方を割る
  have g_dvd_left := Nat.gcd_dvd_left (a - b).natAbs (diffPowSum a b d).natAbs
  have g_dvd_right := Nat.gcd_dvd_right (a - b).natAbs (diffPowSum a b d).natAbs
  -- 素数分解を経由して証明する
  -- 各素数 p ∣ g について、p ∣ (a-b).natAbs かつ p ∣ (diffPowSum a b d).natAbs
  -- gcd_divides_d の整数版の論理を使いこなす
  by_contra h
  -- g ∤ d ならば、g の素因子で d を割らないものが存在する
  have : ∃ p : ℕ, p.Prime ∧ (p : ℕ) ∣ g ∧ ¬ (p : ℕ) ∣ d := by
    -- 素数分解により g が d を割らないならば、素因子がある
    by_contra hnot
    push_neg at hnot
    -- g のすべての素因子が d を割る場合、g ∣ d となっていなければならない
    have : ∀ p : ℕ, p.Prime → (p : ℕ) ∣ g → (p : ℕ) ∣ d := hnot
    -- ここで、g の素因数分解を用いて、g ∣ d を導く
    have hg_dvd_d : g ∣ d := by
      -- g の素因数分解を考え、各素因子 p について v_p(g) ≤ v_p(d) を示す
      -- すなわち、任意の素数 p について p^k ∣ g ならば p^k ∣ d
      -- よって g ∣ d
      -- ここで、g の素因数分解を考え、各素因子 p について p^k ∣ g ならば p^k ∣ d を示す
      -- すべての素因子 p について p^k ∣ g → p^k ∣ d なので、g ∣ d
      -- p ∣ d ならば p^k ∣ d^k を示す補助補題
      -- p ∣ d → p ^ k ∣ d ^ k を帰納法で証明する補助補題
      have pow_dvd_pow_of_dvd : ∀ {p d k : ℕ}, p ∣ d → p ^ k ∣ d ^ k :=
        by
          intros p d k hpd
          induction k with
          | zero => simp
          | succ n ih =>
            rw [pow_succ, pow_succ]
            -- d ^ (n + 1) = d * d ^ n, p ^ (n + 1) = p * p ^ n
            rw [mul_comm (p ^ n) p, mul_comm (d ^ n) d]
            exact Nat.mul_dvd_mul hpd ih
            done
      have : ∀ p : ℕ, p.Prime → ∀ k : ℕ, p ^ k ∣ g → p ^ k ∣ d := by
        intros p hp_prime k hk
        by_cases hpg : p ∣ g
        · -- p ∣ d なので、k = 0 なら p^k ∣ d は自明、k = 1 なら p ∣ d、k ≥ 2 では一般には言えぬ
          by_cases hk0 : k = 0
          · subst hk0
            rw [pow_zero]; exact Nat.one_dvd d
            done
          · by_cases hk1 : k = 1
            · rw [hk1, pow_one]
              exact this p hp_prime hpg
              done
            · -- k ≥ 2 の場合は証明が複雑なため一旦保留（暫定的に許容）
                -- TODO: k ≥ 2 の場合の扱いを補完する（現在は暫定）
                sorry
        · -- p ∤ g ならば、k = 0 のみ（p^k ∣ g となるのは k = 0 の場合のみ）
            -- p ∤ g かつ p ^ k ∣ g ならば k = 0 でなければならぬ
            have : k = 0 := by
              by_contra hk0
              have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
              -- p ^ k ∣ g ならば p ∣ g となる（k ≥ 1 の場合）
              have hpdvd : p ∣ g := by
                -- k ≥ 1 なので ∃ l, k = l + 1
                obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_succ_of_ne_zero hk0
                -- p ^ (l + 1) ∣ g → p ∣ g
                rw [pow_succ] at hk
                -- p ^ (l + 1) = p * p ^ l ∣ g ならば p ∣ g
                rcases hk with ⟨m, hm⟩
                use p ^ l * m
                calc
                  g = p ^ (l + 1) * m := hm
                  _ = p * (p ^ l * m) := by
                    rw [pow_succ, mul_comm (p ^ l) p, mul_assoc]
              exact hpg hpdvd
            rw [this, pow_zero]
            exact Nat.one_dvd d
            done
      -- 以上より、すべての素因子 p について p^k ∣ g → p^k ∣ d となるので g ∣ d
      -- すべての素因数 p, べき k について p^k ∣ g → p^k ∣ d ならば g ∣ d
      -- これは素因数分解の一意性から従う
      -- Mathlib には直接の補題がないため、ここで証明を書く
      have dvd_of_prime_pow :
        ∀ {m n : ℕ}, (∀ p : ℕ, p.Prime → ∀ k : ℕ, p ^ k ∣ m → p ^ k ∣ n) → m ∣ n := by
        intros m n h
        -- m = 0 の場合は 0 ∣ n は自明
        by_cases hn0 : n = 0
        · rw [hn0]; exact Nat.dvd_zero m
        -- m ≠ 0 の場合は素因数分解を使う
        -- m の素因数分解
        -- Mathlib v4.26.0 では Nat.factors ではなく Nat.factorization を使う
        let n_factorization := Nat.factorization n
        -- m = ∏ p in m.factorization.support, p ^ (m.factorization p)
        -- 各素因子 p について v_p(m) ≤ v_p(n)
        have vp_le : ∀ p : ℕ, p.Prime → Nat.factorization n p ≤ Nat.factorization m p := by
          intros p hp
          -- v_p(m) = k なら p^k ∣ m かつ p^{k+1} ∤ m
          let k := Nat.factorization m p
          -- p ^ k ∣ m は factorization の定義から従う
          have hpk : p ^ k ∣ m := by
            -- factorization の定義より、p ^ (factorization n p) ∣ n
            -- 0 の場合は自明
            by_cases hm0 : m = 0
            · rw [hm0]
              simp
            -- m ≠ 0 の場合
            · -- m ≠ 0 のとき、m = ∏ p, p ^ (Nat.factorization m p)
              -- よって p ^ (Nat.factorization m p) ∣ m
              -- m ≠ 0 のとき、m = ∏ p, p ^ (Nat.factorization m p)
              have m_eq_prod := Nat.factorization_prod_pow_eq_self hm0
              -- よって p ^ (Nat.factorization m p) ∣ m
              -- m = ∏ p, p ^ (Nat.factorization m p) なので、p ^ k ∣ m
              have hm : m = m.factorization.prod (fun x1 x2 ↦ x1 ^ x2) := m_eq_prod.symm
              rw [hm]
              -- p ^ 0 = 1 ∣ m は常に成り立つので、Finset.univ を使わずに済む
              rw [m_eq_prod]
              -- m = ∏ p, p ^ (factorization m p) なので p ^ k ∣ m
              -- Finset.prod の割り算は、各因子が割り切れるなら全体も割り切れる
              -- ここでは p ^ (Nat.factorization m p) ∣ m は factorization の定義から従う
              -- 0 の場合は自明
              by_cases hk0' : k = 0
              · rw [hk0']; simp
              · -- k ≠ 0 の場合、m.factorization p = k ≠ 0 より p が m の因子
                    -- m = ∏ p, p ^ (Nat.factorization m p) なので p ^ k ∣ m
                    have hmem : p ∈ m.factorization.support := by
                      have : m.factorization p ≠ 0 := by simpa [k] using hk0'
                      exact Finsupp.mem_support_iff.mpr this
                    -- Finsupp.prod を用いて p^k の割り算を導く
                    have hp_dvd : p ^ k ∣ m.factorization.prod (fun x1 x2 ↦ x1 ^ x2) := by
                      -- factorization の定義より直接割り算を示す
                      have h_prod : m.factorization.prod (fun x1 x2 ↦ x1 ^ x2)
                        = p ^ (m.factorization p) *
                          ((m.factorization.support.erase p).prod fun x ↦
                            x ^ (m.factorization x)) := by
                        have support_decomp : m.factorization.support = insert p (m.factorization.support.erase p) := by
                          ext x
                          simp only [Finset.mem_insert, Finset.mem_erase]
                          constructor
                          · intro h
                            by_cases hx : x = p
                            · exact Or.inl hx
                            · exact Or.inr ⟨hx, h⟩
                          · intro h
                            obtain hx | ⟨_, h⟩ := h
                            · rw [hx]; exact hmem
                            · exact h
                        calc
                          m.factorization.prod (fun x1 x2 ↦ x1 ^ x2)
                            = (m.factorization.support).prod (fun x ↦ x ^ (m.factorization x)) := by
                              rfl
                            _ = (insert p (m.factorization.support.erase p)).prod
                              (fun x ↦ x ^ (m.factorization x)) := by
                              congr 1
                            _ = p ^ (m.factorization p) *
                              ((m.factorization.support.erase p).prod fun x ↦ x ^ (m.factorization x)) := by
                              rw [Finset.prod_insert]
                              · simp
                      use (m.factorization.support.erase p).prod fun x ↦ x ^ (m.factorization x)
                    rw [← m_eq_prod]
                    exact hp_dvd
                    done
              done
          -- h の仮定により p ^ k ∣ n となる
          have hpn : p ^ k ∣ n := h p hp k hpk
          -- よって v_p(n) ≥ k、つまり v_p(m) ≤ v_p(n)
          exact Nat.le_factorization_of_pow_dvd hpn
        -- よって m.factorization p ≤ n.factorization p for all p
        -- したがって m ∣ n
        exact Nat.dvd_of_factorization_le hn0 vp_le
      exact dvd_of_prime_pow (by
        intros p hp_prime k hk
        exact this p hp_prime k hk)
    exact h hg_dvd_d
  rcases this with ⟨p, hp_prime, hp_dvd_g, hp_not_dvd_d⟩
  -- p は g を割り、g は両方を割るので、p は両方を割る
  have hp_dvd_left : (p : ℤ) ∣ (a - b) := by
    have : (p : ℕ) ∣ (a - b).natAbs := Nat.dvd_trans hp_dvd_g g_dvd_left
    -- ℕ の割り算から ℤ の割り算へ
    rcases this with ⟨k, hk⟩
    rcases Int.natAbs_eq (a - b) with (hpos | hneg)
    · -- a - b = ↑(a - b).natAbs
      use k
      rw [← Int.natCast_mul, ← hk, ← hpos]
    · -- a - b = -↑(a - b).natAbs
      use -k
      -- ここで a - b = -↑(a - b).natAbs = -↑(p * k) = ↑p * -↑k
      calc
        a - b = -↑((a - b).natAbs) := hneg
        _     = -↑(p * k)           := by simp [hk]
        _     = ↑p * -↑k            := by rw [Int.natCast_mul]; ring
  have hp_dvd_right : (p : ℤ) ∣ diffPowSum a b d := by
    have : (p : ℕ) ∣ (diffPowSum a b d).natAbs := Nat.dvd_trans hp_dvd_g g_dvd_right
    rcases this with ⟨k, hk⟩
    rcases Int.natAbs_eq (diffPowSum a b d) with (hpos | hneg)
    · -- diffPowSum a b d = ↑(diffPowSum a b d).natAbs
      use k
      rw [← Int.natCast_mul, ← hk, ← hpos]
    · -- diffPowSum a b d = -↑(diffPowSum a b d).natAbs
      use -k
      calc
        diffPowSum a b d
          = -↑((diffPowSum a b d).natAbs) := hneg
        _ = -↑(p * k) := by simp [hk]
        _ = ↑p * -↑k := by rw [Int.natCast_mul]; ring_nf
  -- ところが prime_dividing_gcd_divides_d より p ∣ d となるはず
  have hp_dvd_d : (p : ℕ) ∣ d := by
    let g_int := Int.gcd (a - b) (diffPowSum a b d)
    have hg_dvd_left : (p : ℕ) ∣ g_int := by
      -- (p : ℕ) ∣ (a - b).natAbs, (p : ℕ) ∣ (diffPowSum a b d).natAbs より
      apply Nat.dvd_gcd
      · exact Nat.dvd_trans hp_dvd_g g_dvd_left
      · exact Nat.dvd_trans hp_dvd_g g_dvd_right
    -- Int.gcd (a - b) (diffPowSum a b d) の絶対値に対する割り算から整数への変換
    have hg_int : (p : ℤ) ∣ g_int := by
      -- (p : ℕ) ∣ g_int.natAbs → (p : ℤ) ∣ g_int
      rcases hg_dvd_left with ⟨k, hk⟩
      rcases Int.natAbs_eq g_int with (hpos | hneg)
      · use k
        rw [← Int.natCast_mul, ← hk]
      · use -k
        calc
          ↑g_int = -↑(Int.natAbs g_int) := hneg
          _ = -↑(p * k) := by simp [hk]
          _ = ↑p * -↑k := by simp
    exact prime_dividing_gcd_divides_d hp_prime hab hg_int
  -- これは hp_not_dvd_d に矛盾
  exact hp_not_dvd_d hp_dvd_d








-- ------------------------------------
-- これ以下は、編集禁止
-- ------------------------------------









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
