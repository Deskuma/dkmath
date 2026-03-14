/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- see: [FLT/Basic.lean](/lean/dk_math/DkMath/FLT/Basic.lean)

/-
BinomTail.lean — 二項展開の尾項（k≥2 部分）の共通補題群

目的：`h_div_u2` のような "二項展開の m≥2 項は a^2 を因子に持つ" という主張を
外出しして再利用しやすくする。

設計：
- 汎用版：CommSemiring 上での等式（存在型 / 明示形）
- Nat 版：割り切り（u^2 ∣ ...）が直接使える便利補題

-/

import Mathlib

set_option linter.style.emptyLine true
set_option linter.unusedTactic false

namespace DkMath.Algebra.BinomTail

open scoped BigOperators

section BinomTail

variable {α : Type*}

/- 加法（CommSemiring）上の尾項表示（明示形）
`(a + b)^n - b^n - n * b^(n-1) * a = a^2 * H` を右辺の `H` を明示して返す。
前提は `2 ≤ n`（m≥2 の項が存在するため）。 -/
/-- 加法版（存在形）：`(a+b)^n = b^n + n*b^(n-1)*a + a^2 * H` を与える -/
lemma add_pow_tail_exists [CommSemiring α] (a b : α) {n : ℕ} (hn : 2 ≤ n) :
    ∃ H : α, (a + b) ^ n = b ^ n + (n : α) * b ^ (n - 1) * a + a ^ 2 * H := by
  -- witness: the explicit tail sum
  let S := ∑ k ∈ Finset.range (n - 1), (n.choose (k + 2) : α) * a ^ k * b ^ (n - 2 - k)
  use S
  have sum_full := add_pow a b n
  -- match the order used in `add_pow a b n` (a^k * b^(n-k) * choose)
  let f := fun k => a ^ k * b ^ (n - k) * (n.choose k : α)
  have h_split :
    ∑ k ∈ Finset.range (n + 1), f k
      = b ^ n + (n : α) * b ^ (n - 1) * a + ∑ k ∈ Finset.range (n - 1), f (k + 2) := by
    -- split into k = 0,1 and k ≥ 2, then reindex the latter to range (n-1)
    have h1 := Finset.sum_range_add_sum_Ico f (by linarith : 2 ≤ n + 1)
    have h2 : ∑ k ∈ Finset.range 2, f k = b ^ n + (n : α) * b ^ (n - 1) * a := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      simp [f, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, pow_one]
      ring
    have h3 : ∑ k ∈ Finset.Ico 2 (n + 1), f k = ∑ k ∈ Finset.range (n - 1), f (k + 2) := by
      -- reindex k ↦ k - 2 from Ico 2 (n+1) to range (n-1)
      apply Finset.sum_bij (fun (k : ℕ) _ => k - 2)
      · -- ⊢ ∀ a ∈ Ico 2 (n + 1), a - 2 ∈ range (n - 1)
        intros k hk
        -- k ∈ Ico 2 (n+1) ↦ k-2 ∈ range (n-1)
        simp only [Finset.mem_Ico] at hk
        rcases hk with ⟨hk2, hk3⟩
        -- k ≥ 2, k < n+1 ⇒ k-2 < n-1
        have : k - 2 < n - 1 := by omega
        exact Finset.mem_range.mpr this
      · -- ⊢ ∀ a₁ ∈ Ico 2 (n + 1), ∀ a₂ ∈ Ico 2 (n + 1), a₁ - 2 = a₂ - 2 → a₁ = a₂
        intros a₁ ha₁ a₂ ha₂ h_eq
        -- a₁ - 2 = a₂ - 2 → a₁ = a₂
        grind => instantiate only [= Finset.mem_Ico]
      · -- ⊢ ∀ b ∈ range (n - 1), ∃ a, ∃ (_ : a ∈ Ico 2 (n + 1)), a - 2 = b
        intros k hk
        -- k ∈ range (n-1) ↦ k+2 ∈ Ico 2 (n+1)
        simp only [Finset.mem_range] at hk
        -- hk : k < n - 1
        -- k ∈ range (n-1) ↦ k+2 ∈ Ico 2 (n+1)
        -- 2 ≤ k+2, k+2 < n+1
        have h1 : 2 ≤ k + 2 := by linarith
        have h2 : k + 2 < n + 1 := by omega
        simp only [Finset.mem_Ico]
        use k + 2
        use ⟨h1, h2⟩
        rfl
      · -- ⊢ ∀ a ∈ Ico 2 (n + 1), f a = f (a - 2 + 2)
        intros a ha
        -- ha : a ∈ Ico 2 (n+1), so ha : 2 ≤ a ∧ a < n+1
        have h : a - 2 + 2 = a := by grind => instantiate only [= Finset.mem_Ico]
        simp [h]
        -- f (a) = f (a)
    rw [h1.symm, h2, h3]
  -- the `sum_full` uses the explicit summand while `h_split` was proved using `f`,
  -- make them syntactically equal before rewriting
  have h_sum_def : ∑ m ∈ Finset.range (n + 1), a ^ m * b ^ (n - m) * (n.choose m : α)
                 = ∑ k ∈ Finset.range (n + 1), f k := by
    simp [f]
  rw [sum_full, h_sum_def, h_split]
  simp only [f]
  -- factor a^2 out of the tail sum to match the witness `S`'s shape
  have tail_eq :
    ∑ x ∈ Finset.range (n - 1), a ^ (x + 2) * b ^ (n - (x + 2)) * (n.choose (x + 2) : α)
      = a ^ 2 * S := by
    -- pointwise equality of summands after factoring `a^2`
    have : ∑ x ∈ Finset.range (n - 1), a ^ (x + 2) * b ^ (n - (x + 2)) * (n.choose (x + 2) : α)
      = ∑ x ∈ Finset.range (n - 1), a ^ 2 * (n.choose (x + 2) : α) * a ^ x * b ^ (n - 2 - x) := by
      apply Finset.sum_congr rfl; intro x hx; simp only [pow_add]; -- normalize a^(x+2)
      -- rewrite the exponent n - (x + 2) to the form n - 2 - x before finishing by ring
      rw [Nat.add_comm (n := x) (m := 2)]; rw [Nat.sub_sub]; ring
    -- factor `a^2` out of the sum to match the witness `S`
    rw [this]; rw [Finset.mul_sum]; congr 1; ext x; ring
  rw [tail_eq]

/-- Nat 上の割り切り版：`u^2 ∣ ( (u+y)^n - y^n - n*y^(n-1)*u )` 前提は `2 ≤ n`

この補題は `add_pow_tail_exists` を用いて一撃で証明できる。
CommSemiring レベルの存在型から、Nat の割り切りへは witness をそのまま使う。
-/
lemma binom_tail_nat_dvd (u y : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    u ^ 2 ∣ ((u + y) ^ n - y ^ n - n * y ^ (n - 1) * u) := by
  -- CommSemiring レベルの尾項因数分解を使う
  obtain ⟨H, h_tail⟩ := add_pow_tail_exists (α := ℕ) u y hn
  -- h_tail: (u + y) ^ n = y ^ n + (n : ℕ) * y ^ (n - 1) * u + u ^ 2 * H
  -- Nat での等式に変換して witness を得る
  use H
  -- h_tail を用いて (u + y)^n を展開
  have h_eq : ((u + y) ^ n : ℕ) = (y ^ n + n * y ^ (n - 1) * u + u ^ 2 * H : ℕ) := by
    exact_mod_cast h_tail
  -- 左辺を計算
  calc ((u + y) ^ n - y ^ n - n * y ^ (n - 1) * u : ℕ)
      = (y ^ n + n * y ^ (n - 1) * u + u ^ 2 * H) - y ^ n - n * y ^ (n - 1) * u := by
        rw [← h_eq]
    _ = u ^ 2 * H := by omega

/--
For positive naturals `a, b`, every exponent at least `2` produces strictly positive mixed terms in
the binomial expansion. Concretely, `(a + b)^n` is strictly larger than `a^n + b^n`.

This is the reusable “mixed-term positivity” fact behind statements like:
`(a + b)^p` cannot coincide with `a^p + b^p` once `p ≥ 2` and both inputs are positive.
-/
lemma add_pow_gt_sum_pows_nat (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    a ^ (k + 2) + b ^ (k + 2) < (a + b) ^ (k + 2) := by
  induction k with
  | zero =>
      have hab_pos : 0 < a * b := Nat.mul_pos ha hb
      have hmix_pos : 0 < a * b + a * b := by
        omega
      have hlt : a ^ 2 + b ^ 2 < a ^ 2 + b ^ 2 + (a * b + a * b) := by
        exact Nat.lt_add_of_pos_right hmix_pos
      have hexpand : (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + a * b) := by
        ring
      have hgoal : a ^ 2 + b ^ 2 < (a + b) ^ 2 := by
        rw [hexpand]
        exact hlt
      simpa using hgoal
  | succ k ih =>
      have hab_pos : 0 < a + b := by
        omega
      have hmul_lt :
          (a ^ (k + 2) + b ^ (k + 2)) * (a + b) <
            (a + b) ^ (k + 2) * (a + b) := by
        exact Nat.mul_lt_mul_of_pos_right ih hab_pos
      have ha_pow_pos : 0 < a ^ (k + 2) := Nat.pow_pos ha
      have hb_pow_pos : 0 < b ^ (k + 2) := Nat.pow_pos hb
      have hcross_pos : 0 < a ^ (k + 2) * b + b ^ (k + 2) * a := by
        have h1 : 0 < a ^ (k + 2) * b := Nat.mul_pos ha_pow_pos hb
        have h2 : 0 < b ^ (k + 2) * a := Nat.mul_pos hb_pow_pos ha
        omega
      calc
        a ^ (k + 3) + b ^ (k + 3)
            = a ^ (k + 2) * a + b ^ (k + 2) * b := by
                simp [pow_succ, Nat.mul_comm]
        _ < a ^ (k + 2) * a + b ^ (k + 2) * b + (a ^ (k + 2) * b + b ^ (k + 2) * a) := by
              exact Nat.lt_add_of_pos_right hcross_pos
        _ = (a ^ (k + 2) + b ^ (k + 2)) * (a + b) := by
              ring
        _ < (a + b) ^ (k + 2) * (a + b) := hmul_lt
        _ = (a + b) ^ (k + 3) := by
              simp [pow_succ, Nat.mul_comm]

/-- Convenience wrapper of `add_pow_gt_sum_pows_nat` with a `2 ≤ n` hypothesis. -/
lemma add_pow_gt_sum_pows_nat_of_two_le (a b : ℕ) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < a) (hb : 0 < b) :
    a ^ n + b ^ n < (a + b) ^ n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  rw [hk]
  simpa [Nat.add_comm] using add_pow_gt_sum_pows_nat a b ha hb k

/-- Consequently, `(a + b)^n` cannot coincide with `a^n + b^n` once `n ≥ 2` and `a,b > 0`. -/
lemma add_pow_ne_sum_pows_nat_of_two_le (a b : ℕ) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < a) (hb : 0 < b) :
    (a + b) ^ n ≠ a ^ n + b ^ n := by
  exact ne_of_gt (add_pow_gt_sum_pows_nat_of_two_le a b hn ha hb)

end BinomTail

end DkMath.Algebra.BinomTail
