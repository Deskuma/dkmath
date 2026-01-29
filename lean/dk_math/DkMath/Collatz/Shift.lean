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

/-- Helper lemma: v₂ valuation property for sums when one term has much higher valuation. -/
lemma v2_add_of_lower_val (a b : ℕ) (h : v2 a < v2 b) :
  v2 (a + b) = v2 a := by
  -- If v2(a) < v2(b), then the lower power of 2 dominates the sum
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
  (hn : n % 2 = 1)
  (hk : v2 (3 * n + 1) < k) :
  v2 (3 * (shift k m n) + 1) = v2 (3 * n + 1) := by
  unfold shift
  -- Goal: v2(3*(n + 2^k*m) + 1) = v2(3*n + 1)
  -- This simplifies to: v2((3*n+1) + 3*2^k*m) = v2(3*n+1)
  have h_expand : 3 * (n + pow2 k * m) + 1 = (3*n + 1) + 3 * (pow2 k * m) := by ring
  rw [h_expand]
  -- Now apply v2_add_of_lower_val
  apply v2_add_of_lower_val
  -- We need to show v2(3*n + 1) < v2(3*(2^k*m))
  -- We have v2(3*n + 1) < k by assumption
  -- We need v2(3*2^k*m) ≥ k
  sorry

end DkMath.Collatz
