/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.GapGN

#print "file: DkMath.Analysis.DkReal.Interval"

/-!
# Rational gap intervals

This is the finite-observation substrate of `DkReal`.

A `GapInterval` records rational lower and upper observations. Its width and
nonnegative power image are exact rational data; no real-number completion is
needed at this layer.

The interval is closed and ordered. This validity invariant is essential for
the separation estimates used by representation equivalence.

For pairwise comparison, `separation I J` is the finite rational Gap between
two observed interval universes. It is zero in the Merge/overlap state and
positive exactly when one interval is strictly separated from the other.
This finite geometry is the proposed basis for proving totality without
selecting a Mathlib real limit.
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

/-!
## Separation of closed intervals

The separation is zero when the intervals overlap. Otherwise it is the
positive rational gap between the interval lying on the left and the interval
lying on the right. In the totality design this is the comparison Gap inside
the hull, or "comparison Big", containing both intervals.

[TODO: totality/interval] Prove:

* `separation I J = 0` iff `I.lo ≤ J.hi ∧ J.lo ≤ I.hi`;
* strict left separation and strict right separation are mutually exclusive;
* shrinking both intervals cannot decrease a positive separation.
-/

/-- Nonnegative separation between two closed rational intervals. -/
def separation (I J : GapInterval) : ℚ :=
  max 0 (max (I.lo - J.hi) (J.lo - I.hi))

/-- Interval separation is nonnegative. -/
theorem separation_nonneg (I J : GapInterval) : 0 ≤ I.separation J :=
  le_max_left _ _

/-- Interval separation is symmetric. -/
theorem separation_comm (I J : GapInterval) :
    I.separation J = J.separation I := by
  simp only [separation]
  rw [max_comm (I.lo - J.hi)]

/-- An interval has zero separation from itself. -/
@[simp]
theorem separation_self (I : GapInterval) : I.separation I = 0 := by
  simp only [separation]
  have hlo : I.lo - I.hi ≤ 0 := sub_nonpos.mpr I.le_lo_hi
  simp [hlo]

/-- The left-to-right endpoint gap is bounded by interval separation. -/
theorem lo_sub_hi_le_separation (I J : GapInterval) :
    I.lo - J.hi ≤ I.separation J := by
  exact (le_max_left _ _).trans (le_max_right _ _)

/--
Triangle-type estimate for interval separation.

The width of the middle interval appears because a path may enter it at one
endpoint and leave it at the other. Thus `separation` is not literally a metric
on intervals, but it becomes sufficient for an equivalence relation when all
representation widths tend to zero.
-/
theorem separation_triangle (I J K : GapInterval) :
    I.separation K ≤ I.separation J + J.width + J.separation K := by
  apply max_le
  · exact add_nonneg
      (add_nonneg (I.separation_nonneg J) J.width_nonneg)
      (J.separation_nonneg K)
  · apply max_le
    · have hIJ := I.lo_sub_hi_le_separation J
      have hJK := J.lo_sub_hi_le_separation K
      rw [width] at *
      linarith
    · have hKJ := K.lo_sub_hi_le_separation J
      have hJI := J.lo_sub_hi_le_separation I
      rw [separation_comm K J] at hKJ
      rw [separation_comm J I] at hJI
      rw [width] at *
      linarith

/-- Separation of interval sums is bounded by the sum of the separations. -/
theorem separation_add_le (I J K L : GapInterval) :
    (I.add J).separation (K.add L) ≤
      I.separation K + J.separation L := by
  apply max_le
  · exact add_nonneg (I.separation_nonneg K) (J.separation_nonneg L)
  · apply max_le
    · have hIK := I.lo_sub_hi_le_separation K
      have hJL := J.lo_sub_hi_le_separation L
      simp only [add_lo, add_hi]
      linarith
    · have hKI := K.lo_sub_hi_le_separation I
      have hLJ := L.lo_sub_hi_le_separation J
      rw [separation_comm K I] at hKI
      rw [separation_comm L J] at hLJ
      simp only [add_lo, add_hi]
      linarith

/-- Interval separation is bounded by the distance between the lower endpoints. -/
theorem separation_le_abs_lo_sub_lo (I J : GapInterval) :
    I.separation J ≤ |I.lo - J.lo| := by
  apply max_le
  · exact abs_nonneg _
  · apply max_le
    · have habs : I.lo - J.lo ≤ |I.lo - J.lo| := le_abs_self _
      linarith [J.le_lo_hi]
    · have habs : -(I.lo - J.lo) ≤ |I.lo - J.lo| := neg_le_abs _
      linarith [I.le_lo_hi]

/--
The lower-endpoint distance is controlled by interval separation plus both
interval widths.
-/
theorem abs_lo_sub_lo_le (I J : GapInterval) :
    |I.lo - J.lo| ≤ I.separation J + I.width + J.width := by
  rw [abs_le]
  constructor
  · have hJI := J.lo_sub_hi_le_separation I
    rw [separation_comm J I] at hJI
    simp only [width] at *
    have hIwidth : 0 ≤ I.hi - I.lo := sub_nonneg.mpr I.le_lo_hi
    have hJwidth : 0 ≤ J.hi - J.lo := sub_nonneg.mpr J.le_lo_hi
    linarith
  · have hIJ := I.lo_sub_hi_le_separation J
    simp only [width] at *
    have hIwidth : 0 ≤ I.hi - I.lo := sub_nonneg.mpr I.le_lo_hi
    have hJwidth : 0 ≤ J.hi - J.lo := sub_nonneg.mpr J.le_lo_hi
    linarith

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
