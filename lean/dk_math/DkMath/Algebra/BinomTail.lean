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

/-- Nat 上の割り切り版：`u^2 ∣ ( (u+y)^n - y^n - n*y^(n-1)*u )` 前提は `2 ≤ n` -/
lemma binom_tail_nat_dvd (u y : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    u ^ 2 ∣ ((u + y) ^ n - y ^ n - n * y ^ (n - 1) * u) := by
  -- expand (u+y)^n and peel off k=0,1 (then each remaining term has u^2)
  have h_sum_binomial :
      (∑ m ∈ Finset.range (n + 1), u ^ m * y ^ (n - m) * (n.choose m)) = (u + y) ^ n := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using (add_pow u y n).symm
  -- the tail sum after peeling off k=0,1 is exactly the sum of k≥2 terms in the binomial expansion
  have sum_expr : (u + y) ^ n - y ^ n - n * y ^ (n - 1) * u =
      ∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 2) : ℕ) * u ^ (k + 2) * y ^ (n - 2 - k) := by
    -- replace x^n by (u+y)^n - y^n and expand the binomial in canonical order
    simp only [← h_sum_binomial]
    -- peel off k = 0, then k = 1
    rw [Finset.sum_range_succ']
    simp only [pow_zero, tsub_zero, one_mul, Nat.choose_zero_right, mul_one,
      add_tsub_cancel_right, Nat.sub_sub]
    -- reorder summands so `Finset.sum_range_succ'` matches syntactically
    have reorder' : ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℕ) * u ^ (k + 1) * y ^ (n - 1 - k)
      = ∑ k ∈ Finset.range n, u ^ (k + 1) * y ^ (n - 1 - k) * (Nat.choose n (k + 1) : ℕ) := by
      apply Finset.sum_congr rfl; intro k hk; ring
    have reorder :
        (∑ k ∈ Finset.range n,
            (Nat.choose n (k + 1) : ℕ) * u ^ (k + 1) * y ^ (n - (k + 1)))
      =
        (∑ k ∈ Finset.range n,
            u ^ (k + 1) * y ^ (n - (k + 1)) * (Nat.choose n (k + 1) : ℕ)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
      done
    -- そのまま一致するので
    -- rw [reorder] が通る
    rw [← reorder]
    -- ⊢ ∑ k ∈ range n, n.choose (k + 1) * u ^ (k + 1) * y ^ (n - (k + 1)) - n * y ^ (n - 1) * u =
    --   ∑ x ∈ range (n - 1), n.choose (x + 2) * u ^ (x + 2) * y ^ (n - (2 + x))
    have inner_split :
        Finset.sum (Finset.range n) (fun k =>
          (Nat.choose n (k + 1) : ℕ) * u ^ (k + 1) * y ^ (n - 1 - k))
          =
          (Nat.choose n 1 : ℕ) * u * y ^ (n - 1)
            + Finset.sum (Finset.range (n - 1)) (fun k =>
                (Nat.choose n (k + 2) : ℕ) * u ^ (k + 2) * y ^ (n - 2 - k)) := by
      classical
      have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
      -- `sum_range_succ'` を n-1 に適用して頭を分離
      simpa [Nat.sub_add_cancel hn1,
            Finset.sum_range_succ',  -- ← これは `Finset.sum (range ...)` には当たる
            pow_one, Nat.sub_zero,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.sub_sub] using
        (Finset.sum_range_succ'
          (f := fun k =>
            (Nat.choose n (k + 1) : ℕ) * u ^ (k + 1) * y ^ (n - 1 - k))
          (n := n - 1))
    -- 以後も `∑` 記法を避けるなら
    -- rw [inner_split] はこの形の等式に対しては使える
    -- （ターゲット側も Finset.sum で揃えるのがおすすめ）
    have hsub : (fun k => y ^ (n - (k + 1))) = (fun k => y ^ (n - 1 - k)) := by
      funext k
      -- ここが肝：Nat の減算整理
      simp [Nat.sub_sub, Nat.add_comm]
    -- ゴールの左辺 sum を、指数を直した同値な sum に変形
    have rewrite_exp :
        (∑ k ∈ Finset.range n,
            n.choose (k + 1) * u ^ (k + 1) * y ^ (n - (k + 1)))
          =
        (∑ k ∈ Finset.range n,
            n.choose (k + 1) * u ^ (k + 1) * y ^ (n - 1 - k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      -- この1行で指数だけを変形
      -- n - (k+1) = n - 1 - k
      simp only [Nat.sub_sub, Nat.add_comm]
    -- これでゴールを inner_split の形に寄せる
    -- (※ left side は "sum - ..." なので `rewrite_exp` を左側に当てる)
    calc
      (∑ k ∈ Finset.range n,
          n.choose (k + 1) * u ^ (k + 1) * y ^ (n - (k + 1))) - n * y ^ (n - 1) * u
          =
        (∑ k ∈ Finset.range n,
          n.choose (k + 1) * u ^ (k + 1) * y ^ (n - 1 - k)) - n * y ^ (n - 1) * u := by
            simp [rewrite_exp]
      _ = (n.choose 1 * u * y ^ (n - 1) + ∑ k ∈ Finset.range (n - 1),
            n.choose (k + 2) * u ^ (k + 2) * y ^ (n - 2 - k)) - n * y ^ (n - 1) * u := by
            simp [inner_split]
    -- ⊢ n.choose 1 * u * y ^ (n - 1)
    --   + ∑ k ∈ range (n - 1), n.choose (k + 2) * u ^ (k + 2) * y ^ (n - 2 - k)
    --   - n * y ^ (n - 1) * u
    -- = ∑ x ∈ range (n - 1), n.choose (x + 2) * u ^ (x + 2) * y ^ (n - (2 + x))
    -- cancel the k=1 contribution with the `- n * y ^ (n - 1) * u` term
    simp only [Nat.choose_one_right]  -- n.choose 1 = n

    -- ⊢ n * u * y ^ (n - 1)
    --   + ∑ k ∈ range (n - 1), n.choose (k + 2) * u ^ (k + 2) * y ^ (n - 2 - k)
    --   - n * y ^ (n - 1) * u
    -- = ∑ x ∈ range (n - 1), n.choose (x + 2) * u ^ (x + 2) * y ^ (n - (2 + x))
    ring_nf
    -- ⊢ n * u * y ^ (n - 1)
    --   + ∑ x ∈ range (n - 1), u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x)
    --   - n * u * y ^ (n - 1)
    -- = ∑ x ∈ range (n - 1), u ^ 2 * u ^ x * y ^ (n - (2 + x)) * n.choose (2 + x)
    set A : ℕ := n * u * y ^ (n - 1)
    -- ⊢ A + ∑ x ∈ range (n - 1), u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x) - A =
    --   ∑ x ∈ range (n - 1), u ^ 2 * u ^ x * y ^ (n - (2 + x)) * n.choose (2 + x)

    -- ゴール: A + S - A = T
    -- まず左辺を S に簡約
    have hAS : A + (∑ x ∈ Finset.range (n - 1),
          u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x)) - A
        =
        (∑ x ∈ Finset.range (n - 1),
          u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x)) := by
      -- 「S + A - A = S」を作って、可換で並べ替えて使う
      -- Nat.add_sub_cancel S A : S + A - A = S
      -- 左は A + S - A なので、A+S を S+A にしてから発火させる
      -- Case 0: simple is best
      omega
      -- 以下でも通る例
      /- Case 1:
      ```lean
      simp only [A]
      exact
        Nat.add_sub_self_left (n * u * y ^ (n - 1))
          (∑ x ∈ Finset.range (n - 1), u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x))
      ```
      -- Case 2: 非推奨な書き方でも通る (2026/02/15 13:10)
      ```lean
      simpa [A, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.add_sub_cancel
          (∑ x ∈ Finset.range (n - 1),
            u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x))
          A)
      ```
      -/

    -- ゴール左辺を hAS で潰して S = T にする
    -- （これで “例の指数違いだけ” のゴールに戻る）
    -- ここが「あと一手」
    -- ↓
    -- simp [hAS] だと A が残ることがあるので A も展開しておく
    -- simpa [A, hAS]
    rw [hAS]
    -- これでゴールは「指数違いだけ」の等式になっているはず
    -- ⊢ ∑ x ∈ range (n - 1), u ^ 2 * u ^ x * y ^ (n - 2 - x) * n.choose (2 + x) =
    --   ∑ x ∈ range (n - 1), u ^ 2 * u ^ x * y ^ (n - (2 + x)) * n.choose (2 + x)
    refine Finset.sum_congr rfl ?_
    intro x hx
    -- ここで指数だけを正規化
    -- n - (2 + x) を n - 2 - x に
    -- ⊢ u ^ 2 * u ^ x * y ^ (n -  2 - x ) * n.choose (2 + x)
    -- = u ^ 2 * u ^ x * y ^ (n - (2 + x)) * n.choose (2 + x)
    simp [Nat.sub_sub]
    done
    -- goal closed by the `simp` above (no further tactic needed)
  rw [sum_expr]
  apply Finset.dvd_sum
  intro k hk
  simp only [Finset.mem_range] at hk
  -- u^2 divides u^(k+2)
  use (n.choose (k + 2) * u ^ k * y ^ (n - 2 - k))
  ring

end BinomTail

end DkMath.Algebra.BinomTail
