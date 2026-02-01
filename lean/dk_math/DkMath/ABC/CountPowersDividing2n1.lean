/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.ABC.PadicValNat

namespace DkMath.ABC

set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- For odd prime p and k ≥ 1, count of n ≤ X with p^k | (2n+1) is ≤ ⌈(X+1)/p^k⌉
/--
`count_powers_dividing_2n1` は、素数 `p`（ただし `p ≠ 2`）と自然数 `k ≥ 1`、および任意の `X` に対して、
区間 `[0, X]` に含まれる整数 `n` のうち、`p^k` が `2n+1` を割り切るものの個数が
`((X + 1) / p^k)` の天井値（切り上げ）以下であることを主張します。

この補題は、奇数の形 `2n+1` に対して、ある素数のべき乗が割り切る場合の個数を評価するものです。
特に、`p = 2` の場合は除外されており、`p` が奇素数であることが仮定されています。
この評価は、整数範囲内での割り算の性質や、フィルタリングされた有限集合の要素数の上限を与える際に有用です。
-/
lemma count_powers_dividing_2n1
  (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
  ∀ k ≥ 1, ∀ X,
    (Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card
      ≤ ⌈((X : ℝ)+1) / (p^k : ℝ)⌉₊ := by
  classical
  intro k hk X
  -- m = p^k, 2 は (ℤ/mℤ) で可逆 → 一意な r （0 ≤ r < m）あり、2n+1≡0 ⇔ n≡r
  set m := p^k with hm_def
  have hmpos : 0 < m := by rw [hm_def]; exact Nat.pow_pos hp.pos
  -- 2 と p^k は互いに素（p ≠ 2 だから）
  have hunit2 : Nat.Coprime 2 m := by
    rw [hm_def]
    apply Nat.Coprime.pow_right
    -- Show Nat.Coprime 2 p using p ≠ 2 and p.Prime
    have hcop_p2 : Nat.Coprime p 2 := by
      -- use the prime characterization: p coprime to 2 iff ¬ p ∣ 2
      apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
      intro hdiv
      -- p is prime so p > 0
      have hpos : 0 < p := Nat.Prime.pos hp
      -- from p ∣ 2 and positivity deduce p ≤ 2
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
      -- but primes are ≥ 2, so 2 ≤ p
      have hge : 2 ≤ p := hp.two_le
      -- hence p = 2, contradicting the assumption p ≠ 2
      have heq : p = 2 := le_antisymm hle hge
      exact hpodd heq
    exact Nat.Coprime.symm hcop_p2
  -- Card bound: ブロック分割により ≤ ⌈(X+1)/m⌉
  have hcard_le : (Finset.filter (fun n => n ≤ X ∧ m ∣ (2*n+1)) (Finset.Icc 0 X)).card
      ≤ ⌈((X : ℝ)+1) / (m : ℝ)⌉₊ := by
    -- Core strategy: Prove directly using arithmetic progression count
    -- Key: m | (2n+1) ⟺ 2n+1 ≡ 0 (mod m) ⟺ n ≡ r (mod m) for unique r
    -- Since gcd(2,m) = 1, such r exists and is unique mod m

    -- Step 1: Show card ≤ (X+1) (trivial upper bound)
    have h_card_le : (Finset.filter (fun n => n ≤ X ∧ m ∣ (2*n+1)) (Finset.Icc 0 X)).card
        ≤ X + 1 := by
      have h_subset : (Finset.filter (fun n => n ≤ X ∧ m ∣ (2*n+1)) (Finset.Icc 0 X)) ⊆ (Finset.Icc 0 X) := by
        intro n h
        have ⟨hmem, _⟩ := Finset.mem_filter.mp h
        exact hmem
      calc
        (Finset.filter (fun n => n ≤ X ∧ m ∣ (2*n+1)) (Finset.Icc 0 X)).card
            ≤ (Finset.Icc 0 X).card := by
          apply Finset.card_le_card
          exact h_subset
        _ = X + 1 := by
          rw [Nat.card_Icc]
          simp
    -- Step 2: Key insight - since m | (2n+1) is periodic with period m,
    -- solutions form arithmetic progression with common difference m
    -- In [0, X], at most ⌈(X+1)/m⌉ elements of any such progression

    -- Step 3: Use ZMod to show existence of unique residue class
    -- Since Nat.Coprime 2 m, the map n ↦ 2n+1 is bijective mod m
    -- So ∃! r : ZMod m, 2*r + 1 = 0
    -- Equivalently, ∃! r ∈ [0, m), ∀ n, m | (2n+1) ↔ n ≡ r (mod m)

    -- We'll prove: card ≤ ⌈(X+1)/m⌉ by showing:
    -- (a) All solutions satisfy n ≡ r (mod m) for some r
    -- (b) #{n ∈ [0,X] : n ≡ r (mod m)} ≤ ⌈(X+1)/m⌉ (arithmetic progression)

    -- Implementation: Use Nat.count_modEq_card from Mathlib
    -- Key: Since gcd(2, m) = 1, ∃! r, m | (2n+1) ↔ n ≡ r (mod m)

    -- Step A: Find the unique residue r
    -- We need: 2r + 1 ≡ 0 (mod m), i.e., r ≡ -1/2 (mod m)
    -- Since gcd(2, m) = 1, 2 is invertible mod m
    let r := ((m - 1) / 2) % m  -- Approximation: will refine

    -- Step B: Show m | (2n+1) ↔ n ≡ r (mod m)
    have h_equiv : ∀ n, m ∣ (2*n+1) ↔ n % m = r % m := by
      intro n
      -- Strategy: Direct proof using modular arithmetic
      -- Since m = p^k with p odd prime, m is odd
      -- Therefore 2 has an inverse mod m

      -- Show m is odd
      have hmodd : Odd m := by
        rw [hm_def]
        apply Odd.pow
        exact hp.odd_of_ne_two hpodd

      -- r = ((m-1)/2) % m by definition
      -- We'll show: m | (2n+1) ↔ n ≡ ((m-1)/2) [MOD m]

      constructor
      · -- Forward: m | (2n+1) → n % m = r % m
        intro hdiv
        -- Use dvd_iff_mod_eq_zero
        have h0 : (2*n + 1) % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
        -- Key: 2n ≡ -1 ≡ m-1 (mod m)
        have h1 : (2*n) % m = (m - 1) % m := by
          -- From (2n+1) % m = 0, deduce 2n % m = (m-1) % m
          have : (2*n + 1) % m = ((2*n) % m + 1) % m := by
            conv_lhs => rw [Nat.add_mod]
            simp [Nat.mod_eq_of_lt (Nat.one_lt_two.trans_le (hp.two_le.trans (Nat.le_of_dvd hmpos (dvd_pow_self p (Nat.ne_of_gt hk)))))]
          rw [this] at h0
          -- 0 = ((2n) % m + 1) % m
          -- Since (2n) % m < m, either (2n) % m + 1 < m or (2n) % m + 1 = m
          have h_bound : (2*n) % m < m := Nat.mod_lt _ hmpos
          have h_le : (2*n) % m + 1 ≤ m := Nat.succ_le_of_lt h_bound
          have h_eq_m : (2*n) % m + 1 = m := by
            -- If (2n) % m + 1 < m, then ((2n) % m + 1) % m = (2n) % m + 1
            by_cases hlt : (2*n) % m + 1 < m
            · have : ((2*n) % m + 1) % m = (2*n) % m + 1 := Nat.mod_eq_of_lt hlt
              rw [this] at h0
              omega  -- Contradiction: (2n) % m + 1 = 0 but (2n) % m ≥ 0
            · omega  -- If not <, then = by h_le
          -- Therefore (2n) % m = m - 1
          have h_eq : (2*n) % m = m - 1 := by omega
          -- And (m - 1) % m = m - 1 since m ≥ 1 and m - 1 < m
          have h_mod : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega : m - 1 < m)
          rw [h_eq, h_mod]
        -- Since m is odd and gcd(2,m) = 1, we can "divide by 2"
        -- Show n % m = ((m-1)/2) % m = r
        have h2 : n % m = ((m - 1) / 2) % m := by
          -- Key identity for odd m: 2 * ((m-1)/2) = m - 1
          have hident : 2 * ((m - 1) / 2) = m - 1 := by
            have ⟨k, hk⟩ := hmodd
            omega
          -- m = p^k ≥ p ≥ 3 (since p is odd prime and p ≠ 2)
          have hm_ge_3 : m ≥ 3 := by
            calc m = p ^ k := hm_def
              _ ≥ p ^ 1 := Nat.pow_le_pow_right (hp.one_lt.le) hk
              _ = p := pow_one p
              _ ≥ 3 := by
                have : p ≥ 2 := hp.two_le
                omega
          -- From h1: (2n) % m = (m-1) % m
          -- Rewrite using mod multiplication: (2n) % m = (2 % m) * (n % m) % m
          have h_2n_mod : (2*n) % m = ((2 % m) * (n % m)) % m := Nat.mul_mod 2 n m
          have h_m1_mod : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega : m - 1 < m)
          rw [h_2n_mod, h_m1_mod] at h1
          -- Now h1: ((2 % m) * (n % m)) % m = m - 1
          -- Since 2 < m (from m ≥ 3), we have 2 % m = 2
          have h_2_mod : 2 % m = 2 := Nat.mod_eq_of_lt (by omega : 2 < m)
          rw [h_2_mod] at h1
          -- h1: (2 * (n % m)) % m = m - 1
          -- From hident: 2 * ((m-1)/2) = m - 1
          -- So (2 * (n % m)) % m = (2 * ((m-1)/2)) % m
          have h_target : (2 * ((m - 1) / 2)) % m = m - 1 := by
            rw [hident, h_m1_mod]
          -- Since gcd(2, m) = 1, we can cancel 2:
          -- If 2a ≡ 2b (mod m) and gcd(2,m)=1, then a ≡ b (mod m)
          have h_mod_eq : (n % m) % m = ((m - 1) / 2) % m := by
            -- From h1: (2 * (n % m)) % m = m - 1
            -- From h_target: (2 * ((m-1)/2)) % m = m - 1
            -- So (2 * (n % m)) % m = (2 * ((m-1)/2)) % m
            have h_m_sub_1 : m - 1 = 2 * ((m - 1) / 2) := by simp[hident]
            have h_eq : (2 * (n % m)) % m = (2 * ((m - 1) / 2)) % m := by
              rw [h1, h_target]
            -- Mathematical proof (by trichotomy):
            -- If n % m < (m-1)/2: Then 2*(n % m) < 2*((m-1)/2) but they're equal mod m
            --   → m | 2*(diff), and gcd(2,m)=1 → m | diff → diff = 0 (contradiction)
            -- If n % m = (m-1)/2: Done
            -- If n % m > (m-1)/2: Symmetric to first case
            --
            -- This proof requires careful handling of modular arithmetic with differences,
            -- which is technically complex in Lean's nat arithmetic.
            -- The proof is mathematically sound but the formalization is heavy.
            -- TODO: Optimize using ZMod or extract as separate lemma
            let a := n % m
            let b := (m - 1) / 2
            have h_eq_mod : 2 * a % m = 2 * b % m := by
              have : 2 * (n % m) % m = 2 * ((m - 1) / 2) % m := by rw [h1, h_target]
              exact this
            have h_mul_diff : 2 * (a - b) % m = 0 := by
              have : (2 * a - 2 * b) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h_eq_mod
              rw [← Nat.mul_sub_left_distrib 2 a b] at this
              exact this
            have h_dvd_mul : m ∣ 2 * (a - b) := Nat.dvd_of_mod_eq_zero h_mul_diff
            have h_coprime : Nat.Coprime m 2 := Nat.Coprime.symm hunit2
            have h_dvd_diff : m ∣ (a - b) := Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd_mul
            have h_b_lt_m : b < m := by
              have h_lt : m / 2 < m := Nat.div_lt_self hmpos (by decide)
              have h_le : b ≤ m / 2 := Nat.div_le_div_right (Nat.sub_le m 1)
              exact Nat.lt_of_le_of_lt h_le h_lt
            have h_a_lt_m : a < m := Nat.mod_lt n hmpos
            have h_abs_lt : a - b < m ∨ b - a < m := by
              rcases Nat.lt_trichotomy a b with h_lt | h_eq_ab | h_gt
              · right
                have h_le_ab : a ≤ b := Nat.le_of_lt h_lt
                exact lt_of_le_of_lt (Nat.sub_le b a) h_b_lt_m
              · left; rw [h_eq_ab]; simp only [tsub_self]; exact hmpos
              · left; exact Nat.sub_lt_of_lt h_a_lt_m
            -- Core insight: use modular cancellation
            -- From 2*a ≡ 2*b (mod m) and gcd(2,m) = 1, deduce a ≡ b (mod m)
            -- Since a, b < m, this means a = b
            have h_a_eq_b : a = b := by
              -- From h_eq_mod: 2 * a % m = 2 * b % m
              -- and h_coprime: gcd(m, 2) = 1
              -- We want to deduce a = b

              -- Step 1: Since a, b < m, we have a % m = a and b % m = b
              have ha_mod : a % m = a := Nat.mod_eq_of_lt h_a_lt_m
              have hb_mod : b % m = b := Nat.mod_eq_of_lt h_b_lt_m

              -- Step 2: From 2*a ≡ 2*b (mod m), deduce m | 2*(a - b)
              have h_mul_diff : 2 * (a - b) % m = 0 := by
                have : (2 * a - 2 * b) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h_eq_mod
                rw [← Nat.mul_sub_left_distrib 2 a b] at this
                exact this
              have h_dvd_mul : m ∣ 2 * (a - b) := Nat.dvd_of_mod_eq_zero h_mul_diff

              -- Step 3: Since gcd(m, 2) = 1, from m | 2*(a-b) deduce m | (a-b)
              have h_dvd_diff : m ∣ (a - b) := Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd_mul

              -- Step 4: Since a, b < m, we have a - b < m (if a ≥ b) or b - a < m (if b > a)
              -- Combined with m | (a - b), this forces a - b = 0, hence a = b
              have h_diff_zero : a - b = 0 :=
                Nat.eq_zero_of_dvd_of_lt h_dvd_diff (Nat.sub_lt_of_lt h_a_lt_m)

              -- Step 5: From a - b = 0, deduce a ≤ b
              have h_le_ab : a ≤ b := Nat.sub_eq_zero_iff_le.mp h_diff_zero

              -- Step 6: By symmetry, also show b ≤ a to get a = b
              -- From m | (a - b) = 0, we have m | 0 (trivial)
              -- Also need to show m | (b - a). But from a ≤ b and a - b = 0, we get a = b directly!
              -- Actually, a - b = 0 means a ≤ b. Need to show b ≤ a as well.
              -- Alternative: From 2*a ≡ 2*b, by symmetry get 2*b ≡ 2*a, so same argument gives b - a = 0
              have h_dvd_diff' : m ∣ (b - a) := by
                -- From 2*a % m = 2*b % m, we also have 2*b % m = 2*a % m (symmetry)
                have h_eq_mod' : 2 * b % m = 2 * a % m := h_eq_mod.symm
                have h_mul_diff' : 2 * (b - a) % m = 0 := by
                  have : (2 * b - 2 * a) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h_eq_mod'
                  rw [← Nat.mul_sub_left_distrib 2 b a] at this
                  exact this
                have h_dvd_mul' : m ∣ 2 * (b - a) := Nat.dvd_of_mod_eq_zero h_mul_diff'
                exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd_mul'
              have h_diff_zero' : b - a = 0 :=
                Nat.eq_zero_of_dvd_of_lt h_dvd_diff' (Nat.sub_lt_of_lt h_b_lt_m)
              have h_le_ba : b ≤ a := Nat.sub_eq_zero_iff_le.mp h_diff_zero'

              -- Step 7: a ≤ b and b ≤ a imply a = b
              exact Nat.le_antisymm h_le_ab h_le_ba

            -- Finally, show (n % m) % m = ((m - 1) / 2) % m
            rw [Nat.mod_eq_of_lt h_a_lt_m, h_a_eq_b, Nat.mod_eq_of_lt h_b_lt_m]
          -- Final step: (n % m) % m = n % m
          simp only [Nat.mod_mod_of_dvd, dvd_refl] at h_mod_eq
          exact h_mod_eq
        -- r is defined as ((m - 1) / 2) % m, so h2 is exactly what we need
        -- Relate r % m to the expression and combine with h2 to conclude n % m = r % m
        have rmod : r % m = ((m - 1) / 2) % m := by
          dsimp [r]
          simp only [dvd_refl, Nat.mod_mod_of_dvd]
        exact Eq.trans h2 rmod.symm
      · -- Backward: n % m = r % m → m | (2n+1)
        intro hmod
        -- n ≡ ((m-1)/2) [MOD m]
        -- Multiply by 2: 2n ≡ 2*((m-1)/2) = m-1 (mod m)
        have h1 : 2 * ((m - 1) / 2) = m - 1 := by
          rcases hmodd with ⟨k, hk⟩
          -- m = 2*k + 1, so (m - 1) / 2 = k and the identity follows
          have : (m - 1) / 2 = k := by
            rw [hk]; simp
          rw [this]
          -- (2 * k + 1) % m = (m % m) = 0
          rw [hk]
          -- 2 * k + 1 = m なので 2 * k = m - 1
          simp
        -- From n % m = r % m we deduce (2*n + 1) % m = 0
        have h_congr : (2 * n + 1) % m = (2 * r + 1) % m := by
          -- rewrite both sides into the canonical form using add_mod and mul_mod,
          -- then replace n % m by r % m and finish by congruence
          have h1 : (2 * n + 1) % m = (((2 % m) * (n % m)) % m + 1 % m) % m := by
            rw [Nat.add_mod, Nat.mul_mod]
          have h2 : (2 * r + 1) % m = (((2 % m) * (r % m)) % m + 1 % m) % m := by
            rw [Nat.add_mod, Nat.mul_mod]
          rw [h1, h2]
          congr
        -- 2*r + 1 = 2*((m - 1) / 2) + 1
        have h_r : 2 * ((m - 1) / 2) + 1 = m := by
          rcases hmodd with ⟨k, hk⟩
          have hdiv : (m - 1) / 2 = k := by
            rw [hk]; simp
          rw [hdiv, hk]

        -- ⊢ m ∣ 2 * n + 1
        -- (2 * r + 1) % m = m % m = 0

        have h_m_sub_1 : m - 1 = 2 * ((m - 1) / 2) := by simp[h1]
        have h_m_add_1 : m = 2 * ((m - 1) / 2) + 1 := by omega
        have hm_mod_zero : m % m = 0 := Nat.mod_self m

        have h_r_mod : (2 * r + 1) % m = 0 := by
          -- r = ((m - 1) / 2) % m なので、まず r を展開して計算する
          simp only [r]
          -- 2 * r + 1 = 2 * ((m - 1) / 2 % m) + 1
          -- まず加算の mod を分配する
          rw [Nat.add_mod]
          -- 2 * r + 1 の mod を分配する
          rw [Nat.mul_mod]
          -- 2 * ((m - 1) / 2) + 1 = m
          rw [h_m_add_1]
          -- m % m = 0
          simp
        -- これで (2 * r + 1) % m = 0 = (2 * n + 1) % m = 0
        -- まず右辺 (2 * r + 1) % m = 0 を代入する
        rw [h_r_mod] at h_congr
        -- これで (2 * n + 1) % m = 0 が得られるので除算の逆を使って dvd を示す
        exact Nat.dvd_iff_mod_eq_zero.mpr h_congr

    -- Step C: Count via arithmetic progression
    -- #{n ∈ [0, X] : n % m = r % m} ≤ ⌈(X+1)/m⌉
    have h_count : (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X)).card ≤ ⌈((X + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ := by
      -- Use block partition method: divide [0, X] into blocks of size m
      -- Each block contains at most 1 element with n ≡ r (mod m)
      -- Number of blocks is Q := ⌈(X+1)/m⌉

      let Q := ⌈((X + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊

      -- Key lemma: Each block [qm, (q+1)m) ∩ [0, X] contains at most 1 element with n ≡ r
      have h_block_at_most_one : ∀ q < Q,
          ((Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
            (Finset.Icc 0 X)).card) ≤ 1 := by
        intro q hq
        -- Strategy: Show all elements in the filter are equal
        -- Key insight: In block [q*m, (q+1)*m), if n % m = r % m, then n = q*m + (r % m)
        -- This uniquely determines n (if it exists in the block and in [0, X])
        apply Finset.card_le_one.mpr
        intro n1 hn1 n2 hn2
        -- Extract conditions from membership in filter
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
        rcases hn1 with ⟨⟨_, _⟩, hq1_le, hq1_lt, _, hmod1⟩
        rcases hn2 with ⟨⟨_, _⟩, hq2_le, hq2_lt, _, hmod2⟩
        -- Both n1 and n2 are in [q*m, (q+1)*m) and have n % m = r % m
        -- Key: n1 = q*m + (n1 % m) and n2 = q*m + (n2 % m)
        -- Since n1 % m = r % m and n2 % m = r % m, we have n1 % m = n2 % m
        have h_mod_eq : n1 % m = n2 % m := by
          calc n1 % m = r % m := hmod1
            _ = n2 % m := hmod2.symm
        -- From division algorithm: n1 = (n1 / m) * m + (n1 % m)
        have h1_div : n1 = (n1 / m) * m + n1 % m := by
          have h := Nat.div_add_mod n1 m
          rw [mul_comm] at h
          exact h.symm
        have h2_div : n2 = (n2 / m) * m + n2 % m := by
          have h := Nat.div_add_mod n2 m
          rw [mul_comm] at h
          exact h.symm
        -- From q*m ≤ n < (q+1)*m, deduce n / m = q
        have h1_q : n1 / m = q := by
          have h_le : q ≤ n1 / m := Nat.le_div_iff_mul_le hmpos |>.mpr hq1_le
          have h_lt : n1 / m < q + 1 := Nat.div_lt_iff_lt_mul hmpos |>.mpr hq1_lt
          omega
        have h2_q : n2 / m = q := by
          have h_le : q ≤ n2 / m := Nat.le_div_iff_mul_le hmpos |>.mpr hq2_le
          have h_lt : n2 / m < q + 1 := Nat.div_lt_iff_lt_mul hmpos |>.mpr hq2_lt
          omega
        -- Therefore: n1 = q*m + (n1 % m) and n2 = q*m + (n2 % m)
        calc n1 = (n1 / m) * m + n1 % m := h1_div
          _ = q * m + n1 % m := by rw [h1_q]
          _ = q * m + n2 % m := by rw [h_mod_eq]
          _ = (n2 / m) * m + n2 % m := by rw [h2_q]
          _ = n2 := h2_div.symm

      -- Cover [0, X] with Q blocks
      have h_cover : (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X)).card
          ≤ Finset.sum (Finset.range Q) (fun q =>
            (Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
              (Finset.Icc 0 X)).card) := by
        -- Strategy: Show left side is subset of the union of all blocks
        -- For each n with n % m = r % m and n ≤ X, it belongs to block q = n / m
        -- And we need to show q < Q

        -- Use card inequality: card(A) ≤ sum over all blocks
        have h_subset : ∀ n ∈ (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X)),
            ∃ q < Q, n ∈ (Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
              (Finset.Icc 0 X)) := by
          intro n hn
          simp only [Finset.mem_filter, Finset.mem_Icc] at hn
          rcases hn with ⟨⟨hn0, hnX⟩, hmod⟩
          -- Set q := n / m
          use n / m
          constructor
          · -- Show n / m < Q
            -- n ≤ X implies n / m ≤ X / m < (X+1) / m ≤ ⌈(X+1)/m⌉ = Q
            have h_div_le : (n : ℝ) / (m : ℝ) ≤ (X : ℝ) / (m : ℝ) := by
              have h_n_le_X : (n : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr hnX
              exact div_le_div_of_nonneg_right h_n_le_X (Nat.cast_nonneg m)
            have h_le_ceil : (X : ℝ) / (m : ℝ) < ((X + 1 : ℕ) : ℝ) / (m : ℝ) := by
              have h_X_lt : (X : ℝ) < ((X + 1 : ℕ) : ℝ) := by norm_cast; omega
              exact div_lt_div_of_pos_right h_X_lt (Nat.cast_pos.mpr hmpos)
            have h_lt_Q : ((X + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (Q : ℝ) := by
              exact Nat.le_ceil ((X + 1 : ℕ) / (m : ℝ))
            -- Combine to get n / m < Q
            have h_n_div : (n : ℝ) / (m : ℝ) < (Q : ℝ) := by linarith
            -- Convert to natural number inequality
            have h_nat : (n / m : ℕ) < Q := by
              have h_cast : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
                exact Nat.cast_div_le
              have : ((n / m : ℕ) : ℝ) < (Q : ℝ) := by linarith
              exact Nat.cast_lt.mp this
            exact h_nat
          · -- Show n is in the block q
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · exact ⟨hn0, hnX⟩
            · constructor
              · -- q * m ≤ n
                exact Nat.div_mul_le_self n m
              · constructor
                · -- n < (q+1) * m
                  -- From n = (n/m)*m + (n%m) and n%m < m, get n < (n/m)*m + m
                  have h_lt : n < n / m * m + m := by
                    have h_mod := Nat.mod_lt n hmpos
                    have h_div := Nat.div_add_mod n m
                    -- h_div: m * (n / m) + n % m = n
                    -- Need: n < (n / m) * m + m
                    calc n = m * (n / m) + n % m := h_div.symm
                      _ < m * (n / m) + m := by omega
                      _ = (n / m) * m + m := by ring
                  calc n < n / m * m + m := h_lt
                    _ = (n / m + 1) * m := by ring
                · constructor
                  · exact hnX
                  · exact hmod
        -- Use partition argument: each element of S appears in at least one block
        -- Strategy: rewrite left side as card of union, then use subadditivity
        classical
        -- Key: for each n in left side, pick the unique q such that n is in block q
        -- We already know from h_subset that such q exists

        -- Use the fact that card(A) ≤ sum over blocks of card(A ∩ block)
        -- This follows from: A ⊆ ⋃ (A ∩ block_q), which we have from h_subset

        -- Direct approach: use Finset.card_le_card_of_subset after establishing subset relation
        have h_union : (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X))
            ⊆ Finset.biUnion (Finset.range Q) (fun q =>
              (Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
                (Finset.Icc 0 X))) := by
          intro n hn
          simp only [Finset.mem_biUnion, Finset.mem_range]
          -- From h_subset, we get q < Q such that n is in block q
          obtain ⟨q, hq_lt, hq_mem⟩ := h_subset n hn
          exact ⟨q, hq_lt, hq_mem⟩

        -- Now use the covering to bound the card
        -- Each element belongs to at least one block, so card(left) ≤ sum(card(blocks))
        calc (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X)).card
            ≤ (Finset.biUnion (Finset.range Q) (fun q =>
                (Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
                  (Finset.Icc 0 X)))).card := Finset.card_le_card h_union
          _ ≤ Finset.sum (Finset.range Q) (fun q =>
                (Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
                  (Finset.Icc 0 X)).card) := Finset.card_biUnion_le

      -- Each block contributes at most 1, so total ≤ Q
      calc (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X)).card
          ≤ Finset.sum (Finset.range Q) (fun q =>
              (Finset.filter (fun n => q * m ≤ n ∧ n < (q + 1) * m ∧ n ≤ X ∧ n % m = r % m)
                (Finset.Icc 0 X)).card) := h_cover
        _ ≤ Finset.sum (Finset.range Q) (fun _ => 1) := by
            apply Finset.sum_le_sum
            intro q hq
            exact h_block_at_most_one q (Finset.mem_range.mp hq)
        _ = Q := by simp [Finset.sum_const, Finset.card_range]

    -- Step D: Combine
    have h_filter_eq : (Finset.filter (fun n => n ≤ X ∧ m ∣ (2*n+1)) (Finset.Icc 0 X))
        = (Finset.filter (fun n => n % m = r % m) (Finset.Icc 0 X)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨⟨hn0, hnX⟩, hnX', hdiv⟩
        exact ⟨⟨hn0, hnX⟩, (h_equiv n).mp hdiv⟩
      · intro ⟨⟨hn0, hnX⟩, hmod⟩
        constructor
        · exact ⟨hn0, hnX⟩
        · constructor
          · -- Show n ≤ X (already have it)
            exact hnX
          · -- Show m ∣ 2*n+1
            exact (h_equiv n).mpr hmod

    rw [h_filter_eq]
    -- Fix cast issue: ↑(X + 1) vs (↑X + 1)
    convert h_count using 2
    norm_cast  -- Final step: Convert m = p^k back
  simp only [hm_def] at hcard_le
  convert hcard_le using 2
  norm_cast

end DkMath.ABC
