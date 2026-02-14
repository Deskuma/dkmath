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

namespace DkMath.Algebra

open scoped BigOperators
open Finset

section BinomTail

variable {α : Type*}

/-- 加法（CommSemiring）上の尾項表示（明示形）

`(a + b)^n - b^n - n * b^(n-1) * a = a^2 * H` を右辺の `H` を明示して返す。
前提は `2 ≤ n`（m≥2 の項が存在するため）。 -/
lemma add_pow_tail_expr {α : Type*} [CommSemiring α] (a b : α) {n : ℕ} (hn : 2 ≤ n) :
    (a + b) ^ n - b ^ n - (n : α) * b ^ (n - 1) * a
      = a ^ 2 * ∑ k ∈ Finset.range (n - 1), (n.choose (k + 2) : α) * a ^ k * b ^ (n - 2 - k) := by
  -- 展開して m=0,m=1 を取り除き、残りを m↦k+2 で再索引
  rw [add_pow]
  -- (a+b)^n = ∑_{m=0}^n C(n,m) a^m b^{n-m}
  have : (∑ m ∈ Finset.range (n + 1), (n.choose m : α) * a ^ m * b ^ (n - m)) - b ^ n - (n : α) * b ^ (n - 1) * a
    = ∑ k ∈ Finset.range (n - 1), (n.choose (k + 2) : α) * a ^ (k + 2) * b ^ (n - 2 - k) := by
    -- peel off m = 0 and m = 1 then reindex the tail m ↦ k+2
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.sub_zero]
    rw [Finset.sum_range_succ']
    simp only [pow_zero]
    -- remaining tail m = 2..n corresponds to k = 0..n-2 via m = k+2
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Nat.sub_sub, Nat.add_comm]
    rfl
  simpa [mul_assoc, mul_comm, mul_left_comm] using this

/-- 加法版（存在形）：`(a+b)^n = b^n + n*b^(n-1)*a + a^2 * H` を与える。-/
lemma add_pow_tail_exists {α : Type*} [CommSemiring α] (a b : α) {n : ℕ} (hn : 2 ≤ n) :
    ∃ H : α, (a + b) ^ n = b ^ n + (n : α) * b ^ (n - 1) * a + a ^ 2 * H := by
  use ∑ k ∈ Finset.range (n - 1), (n.choose (k + 2) : α) * a ^ k * b ^ (n - 2 - k)
  rw [add_pow_tail_expr a b (hn)]
  ring

/-- Nat 上の割り切り版：`u^2 ∣ ( (u+y)^n - y^n - n*y^(n-1)*u )`。
前提は `2 ≤ n`。-/
lemma binom_tail_nat_dvd (u y : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    u ^ 2 ∣ ((u + y) ^ n - y ^ n - n * y ^ (n - 1) * u) := by
  -- 特殊化して右辺が u^2 * H であることを示す
  have h := add_pow_tail_expr (u : ℕ) (y : ℕ) (hn)
  rw [← h]
  -- RHS = u^2 * (sum ...), 故に u^2 が割り切る
  use (∑ k ∈ Finset.range (n - 1), (n.choose (k + 2) : ℕ) * u ^ k * y ^ (n - 2 - k))
  ring

end BinomTail

end DkMath.Algebra
