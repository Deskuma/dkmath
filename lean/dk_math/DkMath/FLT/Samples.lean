/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic

set_option linter.style.longLine false


example (_a _b _c : ℕ) : True := by
  trivial


-- －－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－
example (a b : ℤ) : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring_nf

example (a b : ℕ) (h : b ≤ a) : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  have h_pow : b ^ 3 ≤ a ^ 3 := Nat.pow_le_pow_left h 3
  zify [h, h_pow]
  ring_nf

example (a b : ℕ) (h : b ≤ a) : a ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) + b ^ 3 := by
  have h_pow : b ^ 3 ≤ a ^ 3 := Nat.pow_le_pow_left h 3
  zify [h, h_pow]
  ring_nf


#check Nat.gcd_add_self_right  -- ∀ q p : ℕ, Nat.gcd q (q + p) = Nat.gcd q p
#check Nat.gcd_self_add_right  -- ∀ q p : ℕ, Nat.gcd (q + p) q = Nat.gcd p q
#check Nat.coprime_iff_gcd_eq_one  -- ∀ {m n : ℕ}, Nat.Coprime m n ↔ Nat.gcd m n = 1
#check Nat.Prime.coprime_iff_not_dvd  -- ∀ {p m : ℕ}, p.Prime → (Nat.Coprime p m ↔ ¬ p ∣ m)

lemma gcd_add_self_right (q p : ℕ) :
  Nat.gcd q (q + p) = Nat.gcd q p := by
  simp only [Nat.gcd_self_add_right]

lemma gcd_eq_one_of_prime_not_dvd
  {p q : ℕ} (hp : p.Prime) (h : ¬ p ∣ q) :
  Nat.gcd q (q + p) = 1 := by
  have : Nat.gcd q p = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm
  simpa [Nat.gcd_add_self_right] using this

/-- Cubic difference formula:
$$
\Large
z^3 - y^3 = (z - y)(z^2 + zy + y^2)\\[16pt]
\normalsize
$$
z: Big := Universe
y: Gap := Unit
-/
def x3sub (y z : ℕ) : ℕ := (z - y) * (z ^ 2 + z * y + y ^ 2)
/--
Cubic power formula:
$$
\Large
x^3 = x \cdot x \cdot x\\[16pt]
\normalsize
$$
x: Body := Geometric Value = (Big - Unit)
-/
def x3pow (x : ℕ) : ℕ := x ^ 3

#eval x3sub 1 3  -- 26
#eval x3pow 3    -- 27

#eval x3sub 1 5  -- 124
#eval x3pow 5    -- 125

#eval x3sub 1 7  -- 342
#eval x3pow 7    -- 343

#eval x3sub 1 9  -- 728
#eval x3pow 9    -- 729

#eval x3sub 1 2  -- 7
#eval x3pow 2    -- 8

#eval x3sub 2 3  -- 19
#eval x3pow 3    -- 27

#eval x3sub 4 5  -- 61
#eval x3pow 4    -- 64

#eval x3sub 5 6  -- 91
#eval x3pow 5    -- 125

/-- 真の立方差公式：z^3 - y^3 = (z - y)(z^2 + zy + y^2) -/
example (y z : ℕ) (h : y ≤ z) : z^3 - y^3 = (z - y) * (z^2 + z * y + y^2) := by
  have h_pow : y^3 ≤ z^3 := Nat.pow_le_pow_left h 3
  zify [h, h_pow]
  ring

namespace BinomTail
open scoped BigOperators

set_option linter.unusedTactic false in
/-- Nat 上の割り切り版：`u^2 ∣ ( (u+y)^n - y^n - n*y^(n-1)*u )` 前提は `2 ≤ n` -/
lemma binom_tail_nat_dvd_standalone (u y : ℕ) {n : ℕ} (hn : 2 ≤ n) :
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
