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

/-- For odd n, v₂(3n+1) ≥ 1. -/
lemma v2_3n_plus_1_ge_1 (n : ℕ) (hn : n % 2 = 1) :
  1 ≤ v2 (3*n + 1) := by
  -- 3n+1 is even when n is odd
  have h_even : (3*n + 1) % 2 = 0 := by omega
  have h_pos : 0 < 3*n + 1 := by omega
  exact Nat.succ_le_of_lt (v2_even (3*n + 1) h_even h_pos)

/-- Multiplicative property: v₂(a * b) = v₂(a) + v₂(b). -/
lemma v2_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
  v2 (a * b) = v2 a + v2 b := by
  -- This property follows from the recursive definition of v2 and the
  -- multiplicative structure of divisibility. The proof requires careful
  -- handling of parity and division.
  sorry

/-- v₂(2^k) = k. -/
lemma v2_pow2 (k : ℕ) : v2 (pow2 k) = k := by
  induction k with
  | zero =>
    unfold v2 pow2
    norm_num
  | succ k' ih =>
    unfold v2 pow2
    norm_num
    sorry

/-- Helper: if 2^s | a but 2^(s+1) ∤ a, then v₂(a) = s. -/
lemma v2_unique (a s : ℕ) (h : v2Spec a s) : v2 a = s := by
  -- This follows from the definition of v2 and the v2Spec property
  unfold v2Spec at h
  obtain ⟨h_divides, h_not_divides⟩ := h
  -- The recursive definition of v2 extracts the exact power
  -- For this, we would need a stronger induction principle or a direct proof
  -- For now, we assert that the definition matches the spec
  sorry

end DkMath.Collatz
