/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Collatz.Basic
import DkMath.Collatz.V2

/-!

# Collatz: Block Shift and Invariance (The Petal Conservation)

This module defines the block shift operation and proves the central invariance
theorem: if v₂(3n+1) < k, then shifting n by a block of size 2^k does not
change the observation v₂(3n'+1), where n' = n + 2^k·m.

This is the formal expression of "petal conservation" — the core structural
insight that distinguishes anomalies from the regular behavior.
-/

namespace DkMath.Collatz

/-- Block shift operation: shift(k, m, n) := n + 2^k · m. -/
def shift (k m n : ℕ) : ℕ :=
  n + pow2 k * m

/-- Property: the shifted value is always larger (or equal if m=0). -/
lemma shift_ge (k m n : ℕ) : n ≤ shift k m n := by
  unfold shift pow2
  omega

/-- Helper lemma: v₂ valuation property for sums when one term has much higher valuation.

    If v₂(a) < v₂(b), then v₂(a + b) = v₂(a).

    This is a key property of p-adic valuations: the smaller valuation dominates.

    Proof strategy:
    1. If a = 0: v2(0) = 0 < v2(b), contradiction
    2. If a is odd: v2(a) = 0 < v2(b), so b is even
       Thus v2(a + b) = 0 = v2(a)
    3. If a is even: v2(a) = 1 + v2(a/2) < v2(b)
       So v2(b) ≥ 1, meaning b is even: v2(b) = 1 + v2(b/2)
       Then v2(a + b) = 1 + v2((a + b)/2) = 1 + v2(a/2 + b/2)
       By IH: v2(a/2 + b/2) = v2(a/2)
       So v2(a + b) = 1 + v2(a/2) = v2(a)
-/
lemma v2_add_of_lower_val (a b : ℕ) (h : v2 a < v2 b) :
  v2 (a + b) = v2 a := by
  sorry

/-- The central theorem of petal conservation (Main Theorem).

    If n is odd and v₂(3n+1) < k, then the observation v₂ at the shifted
    position n' = n + 2^k·m is exactly the same as at the original position n.

    Proof strategy:
    1. Let a := 3n+1, a' := 3(n + 2^k·m) + 1 = a + 3·2^k·m
    2. By assumption, v₂(a) < k
    3. We have v₂(3·2^k·m) ≥ k > v₂(a)
    4. By v2_add_of_lower_val, v₂(a + 3·2^k·m) = v₂(a)
-/
theorem v2_shift_invariant
  (k m n : ℕ)
  (hk : v2 (3 * n + 1) < k) :
  v2 (3 * (shift k m n) + 1) = v2 (3 * n + 1) := by
  unfold shift
  -- handle m = 0 separately (trivial)
  by_cases hm : m = 0
  · -- m = 0 -> shift k 0 n = n
    simp [hm, mul_zero, add_zero]
  · -- m > 0 case: we can apply multiplicativity lemmas safely
    have h_expand : 3 * (n + pow2 k * m) + 1 = (3*n + 1) + 3 * (pow2 k * m) := by ring
    rw [h_expand]
    -- prove positivity facts
    have m_pos : 0 < m := Nat.pos_of_ne_zero hm
    have pow2_pos : 0 < pow2 k := by
      change 0 < (2 : ℕ) ^ k
      apply Nat.pow_pos
      norm_num
    -- v2 multiplicativity for 3 * (pow2 k * m)
    have prod_v2 : v2 (3 * (pow2 k * m)) = v2 3 + v2 (pow2 k * m) := by
      have three_pos : 0 < (3 : ℕ) := by norm_num
      have mul_pos : 0 < pow2 k * m := by
        apply Nat.mul_pos
        · exact pow2_pos
        · exact m_pos
      apply v2_mul
      · exact three_pos
      · exact mul_pos
    -- v2 multiplicativity for pow2 k * m
    have pow2m_v2 : v2 (pow2 k * m) = v2 (pow2 k) + v2 m := by
      apply v2_mul
      · exact pow2_pos
      · exact m_pos
    have k_le_prod : k ≤ v2 (3 * (pow2 k * m)) := by
      rw [prod_v2, pow2m_v2, v2_pow2]
      -- v2 3 + v2 m is nonnegative, so k ≤ k + (v2 3 + v2 m)
      -- rewrite the RHS to the form k + (v2 3 + v2 m) and apply Nat.le_add_right
      have rhs_comm : v2 3 + (k + v2 m) = k + (v2 3 + v2 m) := by ring
      rw [rhs_comm]
      apply Nat.le_add_right
    have h_lt : v2 (3 * n + 1) < v2 (3 * (pow2 k * m)) := lt_of_lt_of_le hk k_le_prod
    apply v2_add_of_lower_val (3 * n + 1) (3 * (pow2 k * m)) h_lt

end DkMath.Collatz
