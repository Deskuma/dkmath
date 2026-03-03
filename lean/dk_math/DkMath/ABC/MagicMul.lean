/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic

#print "file: DkMath.ABC.MagicMul"

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

namespace DkMath.ABC.MagicMul

-- magic mul
example (p q : ℕ) : (1 + p) * (1 + q) = p + p * q + q + 1:= by
  ring

/-- magic_mul の定義 := (1 + p) * (1 + q) -/
def magic_mul (p q : ℕ) := (1 + p) * (1 + q)
/-- magic_mul' の定義 := p + p * q + q + 1 -/
def magic_mul' (p q : ℕ) := p + p * q + q + 1

-- #eval magic_mul 0 0  -- 1
-- #eval magic_mul' 0 0 -- 1

-- #eval magic_mul 2 2  -- 9
-- #eval magic_mul' 2 2 -- 9
-- #eval magic_mul 5 5  -- 36
-- #eval magic_mul' 5 5 -- 36

-- #eval magic_mul 2 3  -- 12
-- #eval magic_mul' 2 3 -- 12
-- #eval magic_mul 5 7  -- 48
-- #eval magic_mul' 5 7 -- 48

-- #eval magic_mul 1 0  -- 2
-- #eval magic_mul' 0 1 -- 2
-- #eval magic_mul 7 0  -- 8
-- #eval magic_mul' 0 7 -- 8

/-- magic_mul / mul' は同値であること -/
@[simp]
lemma magic_mul_eq_plus_one (p q : ℕ) :
  (1 + p) * (1 + q) = p + p * q + q + 1 := by
  ring

/-- magic_mul -1 := (1 + p) * (1 + q) - 1 = p + q + p * q 同値である -/
@[simp]
lemma magic_mul_sub_one (p q : ℕ) :
  (1 + p) * (1 + q) - 1 = p + q + p * q := by
  simp only [magic_mul_eq_plus_one, add_tsub_cancel_right]
  ring_nf

/-- magic_mul := (1 + p) * (1 + q) = r + 1 ↔ p + p * q + q + 1 = r + 1 同値である -/
@[simp]
lemma magic_mul_add_one_iff (p q r : ℕ) :
  (1 + p) * (1 + q) = r + 1 ↔ p + p * q + q + 1 = r + 1 := by
  simp only [magic_mul_eq_plus_one, Nat.add_right_cancel_iff]

/-- magic_mul := r + 1 = (1 + p) * (1 + q) ↔ r + 1 = p + p * q + q + 1 同値である -/
@[simp]
lemma magic_mul_add_one_iff' (p q r : ℕ) :
  r + 1 = (1 + p) * (1 + q) ↔ r + 1 = p + p * q + q + 1 := by
  simp only [magic_mul_eq_plus_one]

/- 全ての自然数 p, q に対して同値である -/
example : ∀ (p q : ℕ), p + q + p * q = (1 + p) * (1 + q) - 1 := by
  intros p q
  simp only [magic_mul_eq_plus_one, add_tsub_cancel_right]
  ring_nf

/-- magic_mul の左辺が 0 でないとき、p ∣ q の同値性を示す -/
@[simp]
lemma dvd_magic_mul_sub_one_left (p q : ℕ) :
  p ∣ ((1+p)*(1+q) - 1) ↔ p ∣ q := by
  rw [magic_mul_sub_one]  -- 展開して p + q + p * q の形にする
  -- p ∣ p + q + p * q を分解
  apply Iff.intro
  · intro h
    -- p ∣ p + q + p * q から p ∣ q を導く
    have h1 : p ∣ p * q := by
      rw [Nat.mul_comm]
      exact Nat.dvd_mul_left p q
    have h2 : p ∣ p := dvd_rfl
    -- p ∣ p + q + p * q から p ∣ q を引き出す
    -- p ∣ p + q + p * q から p ∣ q を導くには、p ∣ p, p ∣ p * q より p ∣ (p + p * q) が成り立つ
    -- そして p ∣ (p + q + p * q) = (p + p * q) + q なので、p ∣ q が必要
    -- 逆向きの証明は、p ∣ q なら p ∣ p + q + p * q も成り立つ
    -- ここは mathlib の dvd_add/dvd_sub を使って分解する
    -- まず p ∣ p + p * q
    have hppq : p ∣ p + p * q := by
      rw [Nat.mul_comm]
      exact Nat.dvd_add dvd_rfl (Nat.dvd_mul_left p q)
    -- そして p ∣ (p + q + p * q) = (p + p * q) + q
    -- よって p ∣ q が必要
    have hq : p ∣ q := by
      -- p ∣ p + q + p * q = (p + p * q) + q
      -- まず p ∣ p + p * q を使って p ∣ (p + p * q) + q から p ∣ q を分解
      -- (p + q + p * q) - (p + p * q) = q
      have h_sub : p + p * q + q - (p + p * q) = q := by
        rw [add_tsub_cancel_left]
      rw [←h_sub]
      apply Nat.dvd_sub
      · rw [add_assoc] at h
        ring_nf at h
        exact h
      · exact hppq
    exact hq
  · intro h
    -- p ∣ q なら p ∣ p + q + p * q を示す
    apply Nat.dvd_add
    · apply Nat.dvd_add
      · exact dvd_rfl  -- p ∣ p
      · exact h  -- p ∣ q
    · exact Nat.mul_comm q p ▸ Nat.dvd_mul_left p q  -- p ∣ p * q

/--
For natural numbers `p` and `q`, `p` divides `(1 + p) * (1 + q) - 1` exactly when `p` divides `q`.

Proof idea: expand `(1 + p) * (1 + q) - 1 = p * (1 + q) + q`. The term `p * (1 + q)` is a multiple of `p`, so the divisibility by `p` of the whole expression is equivalent to the divisibility of `q` by `p`.

用途: モジュラ算術や因子 `(1 + p)` を含む式の簡約でよく使われます。特に `p` での剰余を取る操作の簡略化に便利です。
-/
lemma dvd_magic_mul_sub_one_left' (p q : ℕ) :
  p ∣ ((1+p)*(1+q) - 1) ↔ p ∣ q := by
  rw [magic_mul_sub_one]
  -- p ∣ p + q + p * q ↔ p ∣ q
  constructor
  · intro h
    -- p ∣ p + q + p * q, p ∣ p, p ∣ p * q ⇒ p ∣ q
    have h₁ : p ∣ p := dvd_rfl
    have h₂ : p ∣ p * q := Nat.mul_comm q p ▸ Nat.dvd_mul_left p q
    have h_sum : p ∣ p + p * q := Nat.dvd_add h₁ h₂
    -- p ∣ (p + q + p * q) = (p + p * q) + q ⇒ p ∣ q
    -- (p + q + p * q) - (p + p * q) = q
    have h_sub : p + q + p * q - (p + p * q) = q := by
      ring_nf
      simp only [add_tsub_cancel_left]
    rw [←h_sub]
    exact Nat.dvd_sub h h_sum
    -- h_sub: p + q + p * q - (p + p * q) = q なので、dvd_sub の結果は p ∣ q となる
  · intro h
    -- p ∣ q ⇒ p ∣ p + q + p * q
    apply Nat.dvd_add
    apply Nat.dvd_add
    exact dvd_rfl
    exact h
    exact Nat.mul_comm q p ▸ Nat.dvd_mul_left p q
  -- rad (n + 1) = rad n * 1 = rad n
  -- よって、rad (n + 1) = rad n + 1 を示すには、rad n = n を示せばよい
  -- （rad n ≤ n は既に証明済み）

-- @[simp] ※使わない！永久ループになる！
lemma dvd_magic_mul_sub_one_right (p q : ℕ) :
  q ∣ p ↔ q ∣ ((1+p)*(1+q) - 1) := by
  rw [magic_mul_sub_one]
  constructor
  · intro hqp
    -- q ∣ p ⇒ q ∣ p + q + p * q
    apply Nat.dvd_add
    apply Nat.dvd_add
    exact hqp
    exact dvd_rfl
    exact Nat.dvd_mul_left q p
  · intro h
    -- q ∣ p + q + p * q ⇒ q ∣ p
    -- q ∣ p, q ∣ q, q ∣ p * q ⇒ q ∣ p + q + p * q
    -- 逆向きは p = (p + q + p * q) - (q + p * q)
    have hq : q ∣ q := dvd_rfl
    have hpq : q ∣ p * q := Nat.dvd_mul_left q p
    have hsum : q ∣ q + p * q := Nat.dvd_add hq hpq
    have hsub : p + q + p * q - (q + p * q) = p := by
      simp [tsub_add_eq_tsub_tsub]
      ring_nf
      simp only [add_tsub_cancel_right]
    rw [←hsub]
    exact Nat.dvd_sub h hsum

end DkMath.ABC.MagicMul
