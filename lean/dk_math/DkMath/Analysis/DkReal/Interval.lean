/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.GapGN

#print "file: DkMath.Analysis.DkReal.Interval"

/-!
# Rational gap intervals

This is the first computational substrate for a future `DkReal`.

A `GapInterval` records rational lower and upper observations. Its width and
nonnegative power image are exact rational data; no real-number completion is
needed at this layer.
-/

namespace DkMath.Analysis.DkReal

/-- A closed interval with rational endpoints. -/
structure GapInterval where
  lo : ℚ
  hi : ℚ
  le_lo_hi : lo ≤ hi
deriving Repr

namespace GapInterval

/-- Two rational gap intervals are equal when both endpoints are equal. -/
@[ext]
theorem ext {I J : GapInterval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  cases I
  cases J
  simp_all

/-- The degenerate rational interval containing only `q`. -/
def singleton (q : ℚ) : GapInterval :=
  ⟨q, q, le_rfl⟩

/-- Both endpoints of a singleton interval are its unique value. -/
@[simp]
theorem singleton_lo (q : ℚ) : (singleton q).lo = q := rfl

/-- Both endpoints of a singleton interval are its unique value. -/
@[simp]
theorem singleton_hi (q : ℚ) : (singleton q).hi = q := rfl

/-- Exact rational width of a gap interval. -/
def width (I : GapInterval) : ℚ :=
  I.hi - I.lo

/-- A singleton interval has zero width. -/
@[simp]
theorem singleton_width (q : ℚ) : (singleton q).width = 0 := by
  simp [width]

/-- Every valid gap interval has nonnegative width. -/
theorem width_nonneg (I : GapInterval) : 0 ≤ I.width :=
  sub_nonneg.mpr I.le_lo_hi

/-- The upper endpoint is the lower endpoint plus the interval width. -/
theorem lo_add_width (I : GapInterval) : I.lo + I.width = I.hi := by
  simp [width]

/-!
## Interval arithmetic

Minkowski addition adds corresponding endpoints. On the nonnegative quadrant,
interval multiplication also uses the endpoint products because multiplication
is isotone in each variable there.
-/

/-- Minkowski sum of two rational gap intervals. -/
def add (I J : GapInterval) : GapInterval where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  le_lo_hi := add_le_add I.le_lo_hi J.le_lo_hi

/-- Lower endpoint of an interval sum. -/
@[simp]
theorem add_lo (I J : GapInterval) : (I.add J).lo = I.lo + J.lo := rfl

/-- Upper endpoint of an interval sum. -/
@[simp]
theorem add_hi (I J : GapInterval) : (I.add J).hi = I.hi + J.hi := rfl

/-- Width is additive under Minkowski addition. -/
@[simp]
theorem add_width (I J : GapInterval) :
    (I.add J).width = I.width + J.width := by
  simp [width]
  ring

/--
Product of two nonnegative rational gap intervals.

Both lower-endpoint hypotheses are needed to make endpoint multiplication
order preserving.
-/
def mulNonneg
    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
    GapInterval where
  lo := I.lo * J.lo
  hi := I.hi * J.hi
  le_lo_hi := by
    have hIhi : 0 ≤ I.hi := hI.trans I.le_lo_hi
    exact mul_le_mul I.le_lo_hi J.le_lo_hi hJ hIhi

/-- Lower endpoint of a nonnegative interval product. -/
@[simp]
theorem mulNonneg_lo
    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
    (I.mulNonneg J hI hJ).lo = I.lo * J.lo := rfl

/-- Upper endpoint of a nonnegative interval product. -/
@[simp]
theorem mulNonneg_hi
    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
    (I.mulNonneg J hI hJ).hi = I.hi * J.hi := rfl

/--
The product width is the sum of two first-order interval contributions:
the width of `J` scaled by the upper endpoint of `I`, and the width of `I`
scaled by the lower endpoint of `J`.
-/
theorem mulNonneg_width_eq
    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
    (I.mulNonneg J hI hJ).width
      = I.hi * J.width + J.lo * I.width := by
  simp [width]
  ring

/--
Image of a nonnegative rational interval under the natural power map.

The nonnegativity assumption ensures that endpoint order is preserved.
-/
def powNonneg (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) : GapInterval where
  lo := I.lo ^ d
  hi := I.hi ^ d
  le_lo_hi := by
    have hhi : 0 ≤ I.hi := hlo.trans I.le_lo_hi
    exact pow_le_pow_left₀ hlo I.le_lo_hi d

/-- Lower endpoint of the nonnegative power image. -/
@[simp]
theorem powNonneg_lo (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
    (I.powNonneg d hlo).lo = I.lo ^ d := rfl

/-- Upper endpoint of the nonnegative power image. -/
@[simp]
theorem powNonneg_hi (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
    (I.powNonneg d hlo).hi = I.hi ^ d := rfl

/--
The width after applying a power is exactly the original width multiplied by
the gap-normalized correction kernel.
-/
theorem powNonneg_width_eq
    (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
    (I.powNonneg d hlo).width = I.width * gapGN d I.lo I.width := by
  change I.hi ^ d - I.lo ^ d = I.width * gapGN d I.lo I.width
  rw [← I.lo_add_width]
  exact pow_add_sub_pow_eq_delta_mul_gapGN d I.lo I.width

end GapInterval

end DkMath.Analysis.DkReal
