/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Collatz.Basic

/-!
# Collatz: 2-adic Valuation (v₂)

This module defines the 2-adic valuation v₂(a), which counts the highest power
of 2 dividing a natural number a. This is the core observational quantity for
the accelerated Collatz map.

Definition: v₂(a) = s iff 2^s | a and 2^(s+1) ∤ a.
-/

namespace DkMath.Collatz

/-- The specification for v₂: v₂Spec a s holds iff 2^s divides a and
    2^(s+1) does not divide a.

    This is the core property we reason about; v₂ is extracted from it.
-/
def v2Spec (a s : ℕ) : Prop :=
  (pow2 s ∣ a) ∧ ¬ (pow2 (s+1) ∣ a)

/-- The 2-adic valuation of a natural number a.

    v₂(a) returns the highest exponent s such that 2^s | a.

    Implementation: We recursively divide by 2 until the result is odd.
    This is computable and gives the correct 2-adic valuation.
-/
def v2 (a : ℕ) : ℕ :=
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
  · simp [h_zero, ha]

/-- For even a > 0, v₂(a) > 0. -/
lemma v2_even (a : ℕ) (ha : a % 2 = 0) (h_pos : 0 < a) : 0 < v2 a := by
  unfold v2
  split
  · -- a = 0, contradicts h_pos
    omega
  · split
    · -- a % 2 = 1, contradicts ha
      omega
    · -- a is even and > 0, so 1 + v2(a/2) > 0
      omega

/- even step: peel one 2 from a positive even number -/
lemma v2_step_of_even (a : ℕ) (ha : a % 2 = 0) (hpos : 0 < a) :
  v2 a = 1 + v2 (a / 2) := by
  sorry

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

/- odd multiplier does not affect v2 -/
lemma v2_mul_of_odd_left (a b : ℕ) (ha : a % 2 = 1) (hb : 0 < b) :
  v2 (a * b) = v2 b := by
  sorry

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

/- Multiplicative property: v₂(a * b) = v₂(a) + v₂(b).

    This is a fundamental property of 2-adic valuation.
-/
theorem v2_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
  v2 (a * b) = v2 a + v2 b := by
  sorry

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
    -- 2 * 2^k' ≠ 0
    have ne_zero : ¬(2 * 2 ^ k' = 0) := by
      intro h
      have : 2 ^ k' = 0 := by
        cases Nat.eq_zero_or_pos (2 ^ k') with
        | inl h' => exact h'
        | inr h' =>
          have : 2 * 2 ^ k' > 0 := Nat.mul_pos (by norm_num : 0 < 2) h'
          omega
      have : (2 : ℕ) = 0 ∨ k' ≠ 0 ∧ (2 : ℕ) = 0 := by
        cases k' <;> simp [pow_succ] at this
      omega
    simp only [ne_zero, ↓reduceIte]
    -- (2 * 2^k') % 2 ≠ 1 (it's 0)
    have not_one : ¬((2 * 2 ^ k') % 2 = 1) := by
      rw [Nat.mul_mod]
      norm_num
    simp only [not_one, ↓reduceIte]
    -- (2 * 2^k') / 2 = 2^k'
    have div_eq : (2 * 2 ^ k') / 2 = 2 ^ k' := by
      rw [Nat.mul_div_cancel_left]
      norm_num
    rw [div_eq]
    -- Apply IH
    unfold pow2 at ih
    rw [ih]
    ring


end DkMath.Collatz
