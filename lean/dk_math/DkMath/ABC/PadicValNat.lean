/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.ABC.PadicValNat"

namespace DkMath.ABC

/--
補助補題：v_p(n) の分解
`padicValNat_split` は、p-進値 `padicValNat p n` を 1 以下の最小値と 1 を引いた値の最大値の和に分解する補助補題です。
具体的には、`padicValNat p n` が 0 の場合は 0 に等しくなり、1 の場合は 1 に等しくなり、それ以外の場合はそれらの和に等しくなります。
-/
lemma padicValNat_split (p n : ℕ) :
    padicValNat p n = min (padicValNat p n) 1 + max (padicValNat p n - 1) 0 := by
  by_cases h : padicValNat p n = 0
  · simp [h]
  · by_cases h1 : padicValNat p n = 1
    · simp [h1]
    · have : padicValNat p n ≥ 2 := by omega
      have : min (padicValNat p n) 1 = 1 := by omega
      have : max (padicValNat p n - 1) 0 = padicValNat p n - 1 := by omega
      omega


/-! ### p-adic Valuation Counting Lemmas

For odd primes p, the equation p^k | (2n+1) has exactly one solution modulo p^k
(since 2 is invertible in ℤ/p^kℤ). This gives precise counts for layer-cake sums.
-/


/--
`padic_val_two_of_odd` は、任意の自然数 `n` に対して、`2*n+1` の 2 進 p-進値が 0 であることを示します。
これは、`2*n+1` が奇数であり、2 で割り切れないためです。
証明では、`padicValNat.eq_zero_of_not_dvd` を用いて、2 が `2*n+1` を割り切らないことから結論を導きます。
-/
-- Special case: p = 2, always v_2(2n+1) = 0
lemma padic_val_two_of_odd : ∀ n : ℕ, padicValNat 2 (2*n+1) = 0 := fun n => by
  apply padicValNat.eq_zero_of_not_dvd
  omega

/--
`padic_val_two_of_even` は、任意の自然数 `n` に対して、`2*n` の 2 進 p-進値に関する性質を示します。
具体的には、`n = 0` の場合、`padicValNat 2 (2*n) = 0` かつ `1 + padicValNat 2 n = 1` が成り立ち、
`n ≠ 0` の場合、`padicValNat 2 (2*n) = 1 + padicValNat 2 n` が成り立ちます。
証明では、`n = 0` の場合と `n ≠ 0` の場合に分けて議論し、それぞれのケースで `padicValNat.mul` の性質を利用して結論を導きます。
-/
lemma padic_val_two_of_even (n : ℕ) :
    (n = 0 → padicValNat 2 (2 * n) = 0 ∧ 1 + padicValNat 2 n = 1) ∧
    (n ≠ 0 → padicValNat 2 (2 * n) = 1 + padicValNat 2 n) := by
  constructor
  · intro h
    rw [h, Nat.mul_zero, padicValNat.zero, Nat.add_zero]
    exact ⟨rfl, rfl⟩
  · intro h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) h
    rw [padicValNat.mul (by norm_num) h]
    simp

/-! ### Basic Bounds on p-adic Valuation -/

-- padicValNat p n = 0 ↔ ¬ p ∣ n という補題は mathlib4 に存在する
lemma padicValNat_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
  padicValNat p n = 0 ↔ ¬ p ∣ n := by
  -- mathlib4 の padicValNat.eq_zero_iff は p = 1 ∨ n = 0 ∨ ¬ p ∣ n なので、p.Prime より p ≠ 1
  rw [padicValNat.eq_zero_iff]
  -- p ≠ 1 なので p = 1 は false
  simp only [hp.ne_one, false_or]
  -- n ≠ 0 なので n = 0 は false
  simp only [hn, false_or]

/-- The p-adic valuation of n is at most n itself.

This follows from the fact that p ≥ 2, so p^v ≥ 2^v.
For v ≥ 1: 2^v ≥ v+1 (by induction).
Since p^v | n implies p^v ≤ n, we get v ≤ n.

**Proof sketch:**
1. If n = 0, then padicValNat p 0 = 0 ≤ 0 trivially.
2. If n ≥ 1, let v = padicValNat p n.
3. Then p^v | n, so p^v ≤ n.
4. Since p ≥ 2, we have p^v ≥ 2^v.
5. By induction: 2^v ≥ v+1 for all v ≥ 0.
6. So v+1 ≤ 2^v ≤ p^v ≤ n, giving v ≤ n-1 < n.
-/
lemma padicValNat_le_self (n : ℕ) : padicValNat p n ≤ n := by
  cases n with
  | zero => simp [padicValNat.zero]
  | succ n =>
    -- For n+1 ≥ 1, we use the fact that v ≤ log_p(n+1) ≤ n+1
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
    calc padicValNat p (n + 1)
      _ ≤ Nat.log p (n + 1) := padicValNat_le_nat_log (n + 1)
      _ ≤ n + 1 := Nat.log_le_self _ _

/-- The p-adic valuation of n is at most the logarithm base p of n.

This is a tighter bound than `padicValNat_le_self`.
Note: Mathlib already has `padicValNat_le_nat_log` in
Mathlib.NumberTheory.Padics.PadicVal.Basic:480

**Proof sketch:**
1. If n = 0, trivial.
2. If n ≥ 1, let v = padicValNat p n.
3. Then p^v | n, so p^v ≤ n.
4. Taking log_p of both sides: v ≤ log_p(n).
5. Since v is an integer, v ≤ ⌊log_p(n)⌋ = Nat.log p n.
-/
lemma padicValNat_le_log (p n : ℕ) (_hn : n ≠ 0) : padicValNat p n ≤ Nat.log p n := by
  -- This already exists in Mathlib as padicValNat_le_nat_log
  exact padicValNat_le_nat_log n

lemma Vp_ge_one_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : 1 ≤ padicValNat p n ↔ p ∣ n := by
  -- 1 ≤ padicValNat p n ↔ padicValNat p n ≠ 0 を使う
  have h1 : (padicValNat p n ≥ 1) ↔ (padicValNat p n ≠ 0) := by
    simp [ge_iff_le, Nat.one_le_iff_ne_zero]
  have h0 := padicValNat_eq_zero_iff hp hn
  have h2 : (padicValNat p n ≠ 0) ↔ (p ∣ n) := by
    refine Iff.intro ?mp ?mpr
    · intro hnz
      by_contra hnp
      -- hnp : ¬ p ∣ n
      have : padicValNat p n = 0 := h0.mpr hnp
      contradiction
    · intro hpd
      by_contra hnz
      have : ¬ p ∣ n := h0.mp hnz
      contradiction
  exact Iff.trans h1 h2

lemma padicValNat_one_le_of_prime_dvd {p n : ℕ} (hp : p.Prime) (hnz : n ≠ 0) (hpd : p ∣ n) :
  1 ≤ padicValNat p n := by
  -- p ∣ n かつ n ≠ 0 ならば padicValNat p n ≥ 1 を使う
  have hge := Vp_ge_one_iff hp hnz
  exact hge.mpr hpd

/--
`padicValNat_le_iff_dvd` は、素数 `p` と 0 でない自然数 `n`、および自然数 `k` に対して、
`k ≤ padicValNat p n` と `p ^ k ∣ n` が同値であることを示す補題です。

ここで `padicValNat p n` は、`n` の `p` 進指数（`p` で割り切れる最大のべき指数）を表します。
つまり、`n` が `p^k` で割り切れることと、`n` の `p` 進指数が `k` 以上であることは同値です。

証明では、`mathlib4` の `padicValNat_dvd_iff_le` を型クラスインスタンス `[Fact p.Prime]` を明示的に与えて利用しています。
-/
lemma padicValNat_le_iff_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) :
  k ≤ padicValNat p n ↔ p ^ k ∣ n := by
  -- mathlib4 の padicValNat_dvd_iff_le は [Fact p.Prime] instance を typeclass で要求する
  exact Iff.symm (@padicValNat_dvd_iff_le p (Fact.mk hp) n k hn)
  -- padicValNat_dvd_iff_le : p ^ k ∣ n ↔ k ≤ padicValNat p n
  -- Iff.symm で向きを変える(k ≤ padicValNat p n ↔ p ^ k ∣ n)
  -- Fact.mk hp で Fact p.Prime のインスタンスを明示的に与える（※ここが Mathlib の仮定と異なるところ）
  -- padicValNat_dvd_iff_le は n ≠ 0 の仮定も必要なので hn も与える

/-! ### p-adic Valuation of Powers -/

/--
`padicValNat_pow` は、素数 `p` と 0 でない自然数 `a`、および自然数 `d` に対して、
`padicValNat p (a ^ d) = d * padicValNat p a` が成り立つことを示す補題です。

これは **Lifting the Exponent (LTE) 補題**の基本形であり、
冪乗の p-adic valuation は指数倍になることを表しています。

**証明のポイント:**
- Mathlib の `padicValNat.pow` を使用
- `[Fact p.Prime]` インスタンスを `haveI` で提供
- `a = 0` の場合と `a ≠ 0` の場合を分けて処理

**使用例:**
```lean
example (hp : Nat.Prime 3) (ha : 6 ≠ 0) :
  padicValNat 3 (6 ^ 5) = 5 * padicValNat 3 6 :=
  padicValNat_pow hp 5 ha
```

**数学的意味:**
p が素因数として a に k 回現れるなら、a^d には d*k 回現れます。
これは v_p(a^d) = d · v_p(a) と表記されます。
-/
lemma padicValNat_pow {p a : ℕ} (hp : p.Prime) (d : ℕ) (ha : a ≠ 0) :
    padicValNat p (a ^ d) = d * padicValNat p a := by
  -- Fact インスタンスを用意
  haveI : Fact p.Prime := ⟨hp⟩
  -- Mathlib の padicValNat.pow を適用
  -- padicValNat.pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a
  exact padicValNat.pow d ha

/--
`padicValNat_pow'` は `padicValNat_pow` の変形版で、
0 でない自然数 `a` に対して、`a^d ≠ 0` の条件から `padicValNat p (a ^ d) = d * padicValNat p a` を導きます。

**使用例:**
冪乗が 0 でないことが既知の場合に便利です。
```lean
example (hp : Nat.Prime 3) (hpow : 6 ^ 5 ≠ 0) :
  padicValNat 3 (6 ^ 5) = 5 * padicValNat 3 6 :=
  padicValNat_pow' hp 5 hpow
```
-/
lemma padicValNat_pow' {p a : ℕ} (hp : p.Prime) (d : ℕ) (hpow : a ^ d ≠ 0) :
    padicValNat p (a ^ d) = d * padicValNat p a := by
  by_cases hd : d = 0
  · -- d = 0 の場合：a^0 = 1 で padicValNat p 1 = 0
    subst hd
    simp [padicValNat.one]
  · -- d ≠ 0 の場合：a^d ≠ 0 から a ≠ 0 を導く
    have ha : a ≠ 0 := by
      intro ha_eq
      rw [ha_eq, zero_pow hd] at hpow
      exact hpow rfl
    exact padicValNat_pow hp d ha

/--
`dvd_padicValNat_pow` は、`d ∣ padicValNat p (a ^ d)` が成り立つことを示します。

これは完全冪判定に使われる重要な性質で、
「a^d が完全冪なら、すべての素因数の指数は d の倍数」という事実の基礎となります。

**証明:**
`padicValNat p (a ^ d) = d * padicValNat p a` より、d が因子として現れます。
-/
lemma dvd_padicValNat_pow {p a : ℕ} (hp : p.Prime) (d : ℕ) (ha : a ≠ 0) :
    d ∣ padicValNat p (a ^ d) := by
  rw [padicValNat_pow hp d ha]
  exact dvd_mul_right d _


end DkMath.ABC
