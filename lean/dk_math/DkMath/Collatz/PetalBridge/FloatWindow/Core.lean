/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Basic

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.Core"

namespace DkMath.Collatz

/-!
# Exact upper/lower binary windows

This module uses only natural-number division.  The word `Float` in the module
path means an exact dyadic exponent/mantissa observation; it never means IEEE
floating-point arithmetic or approximation.
-/

/-- Exact binary width, with width zero assigned to the zero word. -/
def bitWidth (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log 2 n + 1

@[simp]
theorem bitWidth_zero : bitWidth 0 = 0 := by
  simp [bitWidth]

theorem bitWidth_eq_log_two_add_one {n : ℕ} (hn : n ≠ 0) :
    bitWidth n = Nat.log 2 n + 1 := by
  simp [bitWidth, hn]

/-- A positive word lies strictly below the power selected by its width. -/
theorem lt_pow_bitWidth {n : ℕ} (hn : 0 < n) :
    n < 2 ^ bitWidth n := by
  rw [bitWidth_eq_log_two_add_one hn.ne']
  exact Nat.lt_pow_succ_log_self (by norm_num) n

/-- The leading bit selected by `bitWidth` is present in a positive word. -/
theorem pow_bitWidth_sub_one_le {n : ℕ} (hn : 0 < n) :
    2 ^ (bitWidth n - 1) ≤ n := by
  rw [bitWidth_eq_log_two_add_one hn.ne']
  simpa using Nat.pow_log_le_self 2 hn.ne'

/-- Lower `w` bits of the raw `3*n+1` step. -/
def lowerWindow3n1 (w n : ℕ) : ℕ :=
  (3 * n + 1) % 2 ^ w

/-- Quotient above the lower `w` bits of the raw `3*n+1` step. -/
def upperCarry3n1 (w n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ w

/-- Exact quotient/remainder reconstruction of the raw step. -/
theorem threeNPlusOne_eq_upperCarry_mul_add_lower (w n : ℕ) :
    3 * n + 1 = upperCarry3n1 w n * 2 ^ w + lowerWindow3n1 w n := by
  simpa [upperCarry3n1, lowerWindow3n1, Nat.add_comm, Nat.mul_comm] using
    (Nat.mod_add_div (3 * n + 1) (2 ^ w)).symm

/-- The lower window is always a valid `w`-bit remainder. -/
theorem lowerWindow3n1_lt_pow (w n : ℕ) :
    lowerWindow3n1 w n < 2 ^ w := by
  exact Nat.mod_lt _ (pow_pos (by norm_num) _)

/-- A state below `2^w` produces an upper carry strictly below three. -/
theorem upperCarry3n1_lt_three_of_lt_pow
    {w n : ℕ} (hn : n < 2 ^ w) :
    upperCarry3n1 w n < 3 := by
  rw [upperCarry3n1, Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) w)]
  omega

/-- Non-strict form of the fixed-width carry upper bound. -/
theorem upperCarry3n1_le_two_of_lt_pow
    {w n : ℕ} (hn : n < 2 ^ w) :
    upperCarry3n1 w n ≤ 2 := by
  exact Nat.le_of_lt_succ (by simpa using upperCarry3n1_lt_three_of_lt_pow hn)

/-- Upper carry observed at the exact current width of a positive state. -/
def stateUpperCarry (n : ℕ) : ℕ :=
  upperCarry3n1 (bitWidth n) n

/-- The own-width carry of a positive state is nonzero. -/
theorem stateUpperCarry_pos {n : ℕ} (hn : 0 < n) :
    0 < stateUpperCarry n := by
  rw [stateUpperCarry, upperCarry3n1,
    Nat.lt_div_iff_mul_lt (pow_pos (by norm_num) (bitWidth n))]
  have hlead := pow_bitWidth_sub_one_le hn
  have hwidth : bitWidth n = (bitWidth n - 1) + 1 := by
    have : 0 < bitWidth n := by
      rw [bitWidth_eq_log_two_add_one hn.ne']
      omega
    omega
  rw [hwidth, pow_succ]
  omega

/-- The own-width carry is exactly one or two. -/
theorem stateUpperCarry_one_or_two {n : ℕ} (hn : 0 < n) :
    stateUpperCarry n = 1 ∨ stateUpperCarry n = 2 := by
  have hpos := stateUpperCarry_pos hn
  have hle : stateUpperCarry n ≤ 2 :=
    upperCarry3n1_le_two_of_lt_pow (lt_pow_bitWidth hn)
  omega

theorem stateUpperCarry_ne_zero {n : ℕ} (hn : 0 < n) :
    stateUpperCarry n ≠ 0 :=
  Nat.ne_of_gt (stateUpperCarry_pos hn)

theorem stateUpperCarry_ne_three {n : ℕ} (hn : 0 < n) :
    stateUpperCarry n ≠ 3 := by
  rcases stateUpperCarry_one_or_two hn with h | h <;> omega

/-- Quotient bounds for the carry at the exact current width. -/
theorem stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow
    (n : ℕ) :
    stateUpperCarry n * 2 ^ bitWidth n ≤ 3 * n + 1 ∧
      3 * n + 1 < (stateUpperCarry n + 1) * 2 ^ bitWidth n := by
  constructor
  · apply (Nat.le_div_iff_mul_le (pow_pos (by norm_num) (bitWidth n))).1
    simp [stateUpperCarry, upperCarry3n1]
  · apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) (bitWidth n))).1
    simp [stateUpperCarry, upperCarry3n1]

/-- Recognize an exact binary width from its enclosing powers of two. -/
theorem bitWidth_eq_add_one_of_pow_le_lt
    {a x : ℕ} (hlo : 2 ^ a ≤ x) (hhi : x < 2 ^ (a + 1)) :
    bitWidth x = a + 1 := by
  have hx : x ≠ 0 := by
    have : 0 < 2 ^ a := pow_pos (by norm_num) a
    omega
  rw [bitWidth_eq_log_two_add_one hx]
  congr 1
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

/--
The raw `3*n+1` word gains exactly its own-width carry in binary width.
-/
theorem bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry
    {n : ℕ} (hn : 0 < n) :
    bitWidth (3 * n + 1) = bitWidth n + stateUpperCarry n := by
  rcases stateUpperCarry_one_or_two hn with hc | hc
  · have hb :=
      stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow n
    rw [hc] at hb
    have hlo : 2 ^ bitWidth n ≤ 3 * n + 1 := by
      simpa using hb.1
    have hhi : 3 * n + 1 < 2 ^ (bitWidth n + 1) := by
      simpa [pow_succ, Nat.mul_comm] using hb.2
    have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
    omega
  · have hb :=
      stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow n
    rw [hc] at hb
    have hlo : 2 ^ (bitWidth n + 1) ≤ 3 * n + 1 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb.1
    have hhi : 3 * n + 1 < 2 ^ ((bitWidth n + 1) + 1) := by
      calc
        3 * n + 1 < 3 * 2 ^ bitWidth n := by
          simpa using hb.2
        _ < 4 * 2 ^ bitWidth n := by
          have hp : 0 < 2 ^ bitWidth n := pow_pos (by norm_num) _
          omega
        _ = 2 ^ ((bitWidth n + 1) + 1) := by
          simp only [pow_succ]
          omega
    have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
    omega

end DkMath.Collatz
