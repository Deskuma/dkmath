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
lemma v2_add_of_lower_val (a b : ℕ) (ha : 0 < a) (h : v2 a < v2 b) :
  v2 (a + b) = v2 a := by
  -- Strong induction on a (note: this lemma is false for a = 0 with our v2(0) = 0 convention)
  revert b ha h
  refine Nat.strongRecOn a (fun a ih => ?_)
  intro b ha h
  by_cases ha_odd : a % 2 = 1
  · -- a is odd, so v2 a = 0, and b must be even (otherwise v2 b = 0)
    have hv2a : v2 a = 0 := v2_odd a ha_odd
    have hb_even : b % 2 = 0 := by
      by_cases hb_even : b % 2 = 0
      · exact hb_even
      · have hb_odd : b % 2 = 1 := by omega
        have hv2b : v2 b = 0 := v2_odd b hb_odd
        have : False := by
          -- h would become 0 < 0
          simp [hv2a, hv2b] at h
        contradiction
    have hab_odd : (a + b) % 2 = 1 := by omega
    rw [v2_odd (a + b) hab_odd, hv2a]
  · -- a is even and positive
    have ha_even : a % 2 = 0 := by omega
    have hv2a_pos : 0 < v2 a := v2_even a ha_even ha
    have hb_even : b % 2 = 0 := by
      by_cases hb_even : b % 2 = 0
      · exact hb_even
      · have hb_odd : b % 2 = 1 := by omega
        have hv2b : v2 b = 0 := v2_odd b hb_odd
        have hv2b_pos : 0 < v2 b := lt_trans hv2a_pos h
        have : False := by
          simp [hv2b] at hv2b_pos
        contradiction
    have hb_pos : 0 < b := by
      by_contra hb0
      push_neg at hb0
      have hb0' : b = 0 := Nat.le_zero.mp hb0
      subst hb0'
      have hlt : v2 a < 0 := by
        simp at h
      exact (Nat.not_lt_zero _ hlt)
    -- write a = 2 * a1 and b = 2 * b1
    rcases Nat.dvd_of_mod_eq_zero ha_even with ⟨a1, rfl⟩
    rcases Nat.dvd_of_mod_eq_zero hb_even with ⟨b1, rfl⟩
    have ha1_pos : 0 < a1 := by
      -- ha : 0 < 2 * a1
      exact Nat.pos_of_mul_pos_left ha
    have hb1_pos : 0 < b1 := by
      -- hb_pos : 0 < 2 * b1
      exact Nat.pos_of_mul_pos_left hb_pos
    have hv2_two : v2 2 = 1 := by
      have : v2 2 = v2 (pow2 1) := by simp [pow2]
      rw [this]
      exact v2_pow2 1
    have hv2a : v2 (2 * a1) = 1 + v2 a1 := v2_two_mul a1 ha1_pos
    have hv2b : v2 (2 * b1) = 1 + v2 b1 := v2_two_mul b1 hb1_pos
    have h_rec : v2 a1 < v2 b1 := by
      have : 1 + v2 a1 < 1 + v2 b1 := by
        rw [hv2a, hv2b] at h
        exact h
      omega
    have ha1_lt : a1 < 2 * a1 := by omega
    have ih_result : v2 (a1 + b1) = v2 a1 :=
      ih a1 (by omega) b1 ha1_pos h_rec
    have hab_pos : 0 < 2 * (a1 + b1) := by
      apply Nat.mul_pos (by decide : 0 < 2)
      omega
    calc
      v2 (2 * a1 + 2 * b1) = v2 (2 * (a1 + b1)) := by ring_nf
      _ = 1 + v2 (a1 + b1) := by
        have hsum_pos : 0 < a1 + b1 := by omega
        exact v2_two_mul (a1 + b1) hsum_pos
      _ = 1 + v2 a1 := by simp [ih_result]
      _ = v2 (2 * a1) := by simp [hv2a]

#print axioms v2_add_of_lower_val

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
    -- Key fact: pow2 k divides (3 * (pow2 k * m))
    have h_dvd : pow2 k ∣ 3 * (pow2 k * m) := by
      use 3 * m
      ring
    -- Therefore k ≤ v2 (3 * (pow2 k * m))
    have k_le_prod : k ≤ v2 (3 * (pow2 k * m)) := by
      have mul_pos : 0 < 3 * (pow2 k * m) := by
        apply Nat.mul_pos
        · norm_num
        · exact Nat.mul_pos pow2_pos m_pos
      exact le_v2_of_pow2_dvd k (3 * (pow2 k * m)) mul_pos h_dvd
    have h_lt : v2 (3 * n + 1) < v2 (3 * (pow2 k * m)) := lt_of_lt_of_le hk k_le_prod
    -- Now we need to show: v2 ((3*n+1) + 3*(pow2 k * m)) = v2 (3*n+1)
    -- This is the p-adic valuation property: if v2(a) < v2(b), then v2(a + b) = v2(a)
    -- For now, we use the general lemma v2_add_of_lower_val
    exact v2_add_of_lower_val (3 * n + 1) (3 * (pow2 k * m)) (by omega) h_lt

#print axioms v2_shift_invariant

end DkMath.Collatz
