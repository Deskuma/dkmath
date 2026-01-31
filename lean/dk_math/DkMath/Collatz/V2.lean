/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.ABC.PadicValNat
import DkMath.Collatz.Basic

/-!
# Collatz: 2-adic Valuation (v₂)

This module defines the 2-adic valuation v₂(a), which counts the highest power
of 2 dividing a natural number a. This is the core observational quantity for
the accelerated Collatz map.

Definition: v₂(a) = s iff 2^s | a and 2^(s+1) ∤ a.
-/

namespace DkMath.Collatz

open DkMath.ABC

/-- The specification for v₂: v₂Spec a s holds iff 2^s divides a and
    2^(s+1) does not divide a.

    This is the core property we reason about; v₂ is extracted from it.
-/
def v2Spec (a s : ℕ) : Prop :=
  (pow2 s ∣ a) ∧ ¬ (pow2 (s+1) ∣ a)

abbrev v2 (a : ℕ) : ℕ := padicValNat 2 a

/-- The 2-adic valuation of a natural number a.

    v₂(a) returns the highest exponent s such that 2^s | a.

    Implementation: We recursively divide by 2 until the result is odd.
    This is computable and gives the correct 2-adic valuation.
-/
def v2' (a : ℕ) : ℕ :=
  if a = 0 then 0
  else if a % 2 = 1 then 0
  else 1 + v2 (a / 2)

/-- v₂(0) = 0 (by definition). -/
lemma v2_zero : v2 0 = 0 := by
  unfold v2
  simp

/-- For odd a, v₂(a) = 0. -/
lemma v2_odd (a : ℕ) (ha : a % 2 = 1) : v2 a = 0 := by
  unfold v2
  by_cases h_zero : a = 0
  · simp [h_zero]
  · -- a ≠ 0 かつ a % 2 = 1（奇数）の場合、padicValNat 2 a = 0
    unfold padicValNat
    -- 奇数なので2で割り切れない
    have h : ¬ 2 ∣ a := by
      rw [Nat.dvd_iff_mod_eq_zero]
      intro contra
      rw [contra] at ha
      simp at ha
    simp [h]

#check padic_val_two_of_even

/-- For even a > 0, v₂(a) > 0. -/
lemma v2_even (a : ℕ) (ha : a % 2 = 0) (h_pos : 0 < a) : 0 < v2 a := by
  unfold v2
  by_cases h_zero : a = 0
  · simp [h_zero] at h_pos
  · -- a ≠ 0 かつ a % 2 = 0 より a > 0 で even
    -- padicValNat 2 a ≥ 1 を示す
    -- padicValNat 2 a は a を 2 で割れる回数
    -- a は 2 で割り切れるので 1 回は割れる
    have h_div : 2 ∣ a := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact ha
    -- a ≠ 0 なので a / 2 < a
    -- padicValNat 2 a = 1 + padicValNat 2 (a / 2)
    have h_v2 : padicValNat 2 a = 1 + padicValNat 2 (a / 2) := by
      -- a は偶数で 0 < a なので、a ≥ 2
      have ha_ge2 : 2 ≤ a := by
        by_contra h_contra
        push_neg at h_contra
        have : a < 2 := h_contra
        have : a ≤ 1 := by omega
        match a with
        | 0 => simp at h_pos
        | 1 => simp at ha
        | n + 2 => omega
      -- a / 2 > 0
      have h_a_div_pos : a / 2 ≠ 0 := by omega
      -- a = 2 * (a / 2) から (a / 2) = a / 2 は当たり前
      have h_div_div : 2 * (a / 2) / 2 = a / 2 := by
        simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      -- padic_val_two_of_even を適用
      have h_result : padicValNat 2 (2 * (a / 2)) = 1 + padicValNat 2 (a / 2) :=
        (padic_val_two_of_even (a / 2)).2 h_a_div_pos
      -- a = 2 * (a / 2) より
      convert h_result using 2
      omega
    -- padicValNat 2 (a / 2) ≥ 0 なので padicValNat 2 a ≥ 1
    have : 0 ≤ padicValNat 2 (a / 2) := Nat.zero_le _
    linarith

/-- peel one 2 from a positive even number -/
lemma v2_step_of_even (a : ℕ) (ha : a % 2 = 0) (hpos : 0 < a) :
  v2 a = 1 + v2 (a / 2) := by
  -- a % 2 = 0 より a = 2 * b と書ける
  obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b := by
    have hdiv : 2 ∣ a := Nat.dvd_iff_mod_eq_zero.mpr ha
    use a / 2
    rw [Nat.mul_div_cancel' hdiv]
  -- b ≠ 0 かつ 2 ≠ 0 を用いる
  have h2_ne : (2 : ℕ) ≠ 0 := by norm_num
  have hb_ne : b ≠ 0 := by
    intro hb0
    simp [hb0] at hpos
  -- v2 (2 * b) = padicValNat 2 (2 * b) なので書き換え
  unfold v2
  -- padicValNat の乗法性を適用して結論を得る
  rw [padicValNat.mul h2_ne hb_ne]
  simp

/-- v₂ as defined recursively equals v₂ as defined via padicValNat.

    This lemma shows that our recursive definition v2' matches the
    standard definition v2 using padicValNat.

    Proof by cases on a:
    - If a = 0, both sides equal 0.
    - If a is odd, both sides equal 0.
    - If a is even and positive, we use the step lemma to peel off factors of 2
      and apply induction.
-/
lemma v2_eq_v2' (a : ℕ) : v2 a = v2' a := by
  unfold v2'
  by_cases h_zero : a = 0
  · -- a = 0 case
    rw [h_zero]
    simp
  · -- a ≠ 0 case
    have h_pos : 0 < a := Nat.pos_of_ne_zero h_zero
    by_cases h_odd : a % 2 = 1
    · -- a is odd
      rw [v2_odd a h_odd]
      simp [h_zero, h_odd]
    · -- a is even
      rw [v2_step_of_even a (by omega) h_pos]
      simp [h_zero, h_odd]

/- even step: peel one 2 from a positive even number -/

/- peeling off the 2 factor -/
lemma v2_two_mul (x : ℕ) (hx : 0 < x) :
  v2 (2 * x) = 1 + v2 x := by
  have h_even : (2 * x) % 2 = 0 := by simp
  have h_pos : 0 < 2 * x := Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) hx
  have h := v2_step_of_even (2 * x) h_even h_pos
  have h_div : (2 * x) / 2 = x := by
    simp only [Nat.mul_div_cancel_left x (by norm_num : 0 < 2)]
  simp only [h_div] at h
  exact h

/-- If 2^k divides a, then k ≤ v₂(a).

    Proof by induction on k: peel off factors of 2 and apply v2_two_mul.
-/
lemma le_v2_of_pow2_dvd (k a : ℕ) (ha : 0 < a) (hdiv : pow2 k ∣ a) :
  k ≤ v2 a := by
  -- Induction on k
  induction k generalizing a with
  | zero =>
    -- 2^0 = 1 divides everything, and v2(a) ≥ 0
    simp
  | succ k ih =>
    -- 2^(k+1) divides a means a = 2 * (2^k * m) for some m
    obtain ⟨m, hm⟩ := hdiv
    have ha_eq : a = 2 * m * (pow2 k) := by
      unfold pow2 at hm
      ring_nf at hm ⊢
      exact hm
    rw [ha_eq]
    -- Now apply v2_two_mul: 2 * m * pow2 k = 2 * (m * pow2 k)
    have h_assoc : 2 * m * pow2 k = 2 * (m * pow2 k) := by ring
    rw [h_assoc]
    have h_m_pos : 0 < m := by
      by_contra hm_neg
      push_neg at hm_neg
      have : m = 0 := Nat.le_zero.mp hm_neg
      subst this
      simp at hm
      have : a = 0 := by simp [ha_eq]
      omega
    have hpos : 0 < m * pow2 k := by
      exact Nat.mul_pos h_m_pos (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
    have h_v2_two : v2 (2 * (m * pow2 k)) = 1 + v2 (m * pow2 k) := v2_two_mul (m * pow2 k) hpos
    rw [h_v2_two]
    -- Now show k ≤ v2 (m * pow2 k) using the inductive hypothesis
    have h_div : pow2 k ∣ m * pow2 k := dvd_mul_left (pow2 k) m
    -- Apply ih to (m * pow2 k)
    have h_ih : k ≤ v2 (m * pow2 k) := ih (m * pow2 k) hpos h_div
    -- Therefore k + 1 ≤ 1 + v2 (m * pow2 k)
    omega

/-- For odd n, v₂(3n+1) ≥ 1. -/
lemma v2_3n_plus_1_ge_1 (n : ℕ) (hn : n % 2 = 1) :
  1 ≤ v2 (3*n + 1) := by
  -- 3n+1 is even when n is odd
  have h_even : (3*n + 1) % 2 = 0 := by omega
  have h_pos : 0 < 3*n + 1 := by omega
  exact Nat.succ_le_of_lt (v2_even (3*n + 1) h_even h_pos)

/-- v₂(2^k) = k.

    This follows directly from the definition of v₂:
    - v₂(2^0) = v₂(1) = 0 ✓
    - v₂(2^(k+1)) = 1 + v₂(2^k) = 1 + k = k+1 by the recursive definition ✓

    This is a fundamental property of 2-adic valuation on powers of 2.
-/
lemma v2_pow2 (k : ℕ) : v2 (pow2 k) = k := by
  -- Proof by induction on k
  induction k with
  | zero =>
    -- Base case: v2(2^0) = v2(1) = 0
    unfold v2 pow2
    simp
  | succ k' ih =>
    -- Inductive step: v2(2^(k'+1)) = k' + 1
    unfold pow2
    show v2 (2 ^ (k' + 1)) = k' + 1
    -- 2^(k'+1) = 2 * 2^k'
    have eq1 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by ring
    rw [eq1]
    -- Now unfold v2
    unfold v2
    -- Use the property that padicValNat 2 (2 * m) = 1 + padicValNat 2 m
    have h_v2_step : padicValNat 2 (2 * 2 ^ k') = 1 + padicValNat 2 (2 ^ k') := by
      have h2_ne : (2 : ℕ) ≠ 0 := by norm_num
      have hk_ne : 2 ^ k' ≠ 0 := by norm_num
      rw [padicValNat.mul h2_ne hk_ne]
      norm_num
    simp only [h_v2_step]
    -- Apply IH
    unfold pow2 at ih
    unfold v2 at ih
    rw [ih]
    ring


end DkMath.Collatz
