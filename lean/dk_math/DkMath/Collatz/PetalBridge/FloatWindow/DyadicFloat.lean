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

/--
Value-free dyadic signature.

Unlike `DyadicFloatObservation`, this record does not retain the original
state.  Equality of signatures therefore expresses observational
compatibility, not state equality.  Any future cardinality theorem must also
account for fixed width, window overlap, and overlap consistency; a zero Gap
width alone is not a uniqueness proof.
-/
structure DyadicFloatSignature where
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

/-- Construct the value-free dyadic signature of a state. -/
noncomputable def dyadicFloatSignature (q r n : ℕ) :
    DyadicFloatSignature where
  width := bitWidth n
  upperBits := q
  lowerBits := r
  upper := upperPrefix q n
  lower := lowerSuffix r n
  carry := stateUpperCarry n
  height := rawHeightLabel n

/-- Forget only the original value and hidden-Gap bookkeeping. -/
def DyadicFloatObservation.signature
    (O : DyadicFloatObservation) : DyadicFloatSignature where
  width := O.width
  upperBits := O.upperBits
  lowerBits := O.lowerBits
  upper := O.upper
  lower := O.lower
  carry := O.carry
  height := O.height

@[simp]
theorem dyadicFloatObservation_signature (q r n : ℕ) :
    (dyadicFloatObservation q r n).signature = dyadicFloatSignature q r n :=
  rfl

/-- Full observation equality implies signature equality, but not conversely. -/
theorem DyadicFloatObservation.signature_eq_of_eq
    {O O' : DyadicFloatObservation} (h : O = O') :
    O.signature = O'.signature := by
  rw [h]

/-- A state is compatible with a value-free signature by exact observation. -/
def DyadicFloatSignature.CompatibleState
    (S : DyadicFloatSignature) (q r n : ℕ) : Prop :=
  dyadicFloatSignature q r n = S

/-- The canonical state is compatible with its own signature. -/
@[simp]
theorem dyadicFloatSignature_compatible_self (q r n : ℕ) :
    (dyadicFloatSignature q r n).CompatibleState q r n :=
  rfl

/-- The requested windows are individually contained in the observed width. -/
def DyadicFloatSignature.WindowsWithinWidth
    (S : DyadicFloatSignature) : Prop :=
  S.upperBits ≤ S.width ∧ S.lowerBits ≤ S.width

/-- The requested upper and lower windows do not overlap. -/
def DyadicFloatSignature.WindowsDisjoint
    (S : DyadicFloatSignature) : Prop :=
  S.upperBits + S.lowerBits ≤ S.width

/-- The requested windows overlap inside the observed word. -/
def DyadicFloatSignature.WindowsOverlap
    (S : DyadicFloatSignature) : Prop :=
  S.width < S.upperBits + S.lowerBits

/-- Disjointness and overlap form the exact arithmetic case split. -/
theorem DyadicFloatSignature.windowsDisjoint_or_windowsOverlap
    (S : DyadicFloatSignature) :
    S.WindowsDisjoint ∨ S.WindowsOverlap := by
  unfold WindowsDisjoint WindowsOverlap
  omega

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
