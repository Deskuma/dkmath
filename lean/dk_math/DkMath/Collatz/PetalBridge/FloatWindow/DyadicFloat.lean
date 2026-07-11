/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat"

namespace DkMath.Collatz

/-!
# Exact dyadic observations

These definitions model a binary word by exact natural-number windows.  No
rounding, approximation, real logarithm, or IEEE floating-point value enters
the API.
-/

/-- The upper `q` bits of `n`, aligned against its exact current width. -/
def upperPrefix (q n : ℕ) : ℕ :=
  n / 2 ^ (bitWidth n - q)

/-- The lower `r` bits of `n`. -/
def lowerSuffix (r n : ℕ) : ℕ :=
  n % 2 ^ r

/-- Number of bits hidden between the observed upper and lower windows. -/
def middleGapWidth (q r n : ℕ) : ℕ :=
  bitWidth n - q - r

/-- Exact candidate capacity left by the unobserved middle Gap. -/
def middleGapCapacity (q r n : ℕ) : ℕ :=
  2 ^ middleGapWidth q r n

/-- One exact upper/lower observation of a natural Collatz state. -/
structure DyadicFloatObservation where
  /-- Observed natural state. -/
  value : ℕ
  /-- Exact binary exponent/word width. -/
  width : ℕ
  /-- Number of requested upper bits. -/
  upperBits : ℕ
  /-- Number of requested lower bits. -/
  lowerBits : ℕ
  /-- Exact upper prefix. -/
  upper : ℕ
  /-- Exact lower suffix. -/
  lower : ℕ
  /-- Width of the unobserved middle word. -/
  gap : ℕ
  /-- Own-width carry of `3*n+1`. -/
  carry : ℕ
  /-- Lower 2-adic height of `3*n+1`. -/
  height : ℕ

/-- Construct the exact dyadic observation at upper/lower window sizes. -/
noncomputable def dyadicFloatObservation (q r n : ℕ) :
    DyadicFloatObservation where
  value := n
  width := bitWidth n
  upperBits := q
  lowerBits := r
  upper := upperPrefix q n
  lower := lowerSuffix r n
  gap := middleGapWidth q r n
  carry := stateUpperCarry n
  height := rawHeightLabel n

/-- A lower suffix is always a valid `r`-bit word. -/
theorem lowerSuffix_lt_pow (r n : ℕ) :
    lowerSuffix r n < 2 ^ r := by
  exact Nat.mod_lt _ (pow_pos (by norm_num) r)

/-- Touching upper and lower windows leave no hidden middle Gap. -/
theorem middleGapWidth_eq_zero_of_width_le_upper_add_lower
    {q r n : ℕ} (h : bitWidth n ≤ q + r) :
    middleGapWidth q r n = 0 := by
  unfold middleGapWidth
  omega

/-- A zero middle Gap has exactly one raw middle-word candidate. -/
theorem middleGapCapacity_eq_one_of_width_le_upper_add_lower
    {q r n : ℕ} (h : bitWidth n ≤ q + r) :
    middleGapCapacity q r n = 1 := by
  simp [middleGapCapacity,
    middleGapWidth_eq_zero_of_width_le_upper_add_lower h]

@[simp]
theorem dyadicFloatObservation_width (q r n : ℕ) :
    (dyadicFloatObservation q r n).width = bitWidth n := rfl

@[simp]
theorem dyadicFloatObservation_gap (q r n : ℕ) :
    (dyadicFloatObservation q r n).gap = middleGapWidth q r n := rfl

end DkMath.Collatz
