/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Order

#print "file: DkMath.Analysis.DkReal.CanonicalOrder"

/-!
# Canonical order by nonnegative Gap extraction

This module interprets `x ≤ y` without adding subtraction to `DkNNRealQ`.
Instead, it extracts a nonnegative Gap universe `z` satisfying

`y = x + z`.

For representative intervals `Xₙ` and `Yₙ`, the safe Gap observation is

`[max 0 (Yₙ.lo - Xₙ.hi), max 0 (Yₙ.hi - Xₙ.lo)]`.

The lower endpoint is the part of `Y` known to lie beyond all of `X`; the
upper endpoint is the largest Gap still compatible with the observations.
This construction uses rational endpoint subtraction internally, but exposes
only an additive existence theorem on the quotient.

In Cosmic Formula language:

* `Body = x`;
* the extracted nonnegative universe is `Gap = z`;
* `Big = x + z = y`.

Applying a natural power afterwards is governed by the existing exact identity

`(x + z)^d = x^d + z * gapGN d x z`.
-/

namespace DkMath.Analysis.DkReal

/-!
## I. Finite Gap extraction
-/

/-- Safe nonnegative Gap interval extracted from two stage observations. -/
def diffNonnegInterval (I J : GapInterval) : GapInterval where
  lo := max 0 (J.lo - I.hi)
  hi := max 0 (J.hi - I.lo)
  le_lo_hi := by
    apply max_le_max_left
    exact sub_le_sub J.le_lo_hi I.le_lo_hi

/-- The extracted Gap has a nonnegative lower endpoint. -/
theorem diffNonnegInterval_lo_nonneg (I J : GapInterval) :
    0 ≤ (diffNonnegInterval I J).lo :=
  le_max_left _ _

/-- Width of an extracted Gap is bounded by the sum of the input widths. -/
theorem diffNonnegInterval_width_le (I J : GapInterval) :
    (diffNonnegInterval I J).width ≤ I.width + J.width := by
  simp only [diffNonnegInterval, GapInterval.width]
  by_cases hlo : J.lo - I.hi ≤ 0
  · rw [max_eq_left hlo]
    by_cases hhi : J.hi - I.lo ≤ 0
    · rw [max_eq_left hhi]
      linarith [I.le_lo_hi, J.le_lo_hi]
    · rw [max_eq_right (le_of_not_ge hhi)]
      linarith [I.le_lo_hi, J.le_lo_hi]
  · have hlo' : 0 ≤ J.lo - I.hi := le_of_not_ge hlo
    rw [max_eq_right hlo']
    have hhi : 0 ≤ J.hi - I.lo := by
      linarith [I.le_lo_hi, J.le_lo_hi]
    rw [max_eq_right hhi]
    linarith

/-- Stagewise extraction of the nonnegative Gap from `x` to `y`. -/
def diffNonnegApprox
    (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
  diffNonnegInterval (x.interval n) (y.interval n)

/-- Extracted Gap intervals remain nested. -/
theorem diffNonnegApprox_nested
    (x y : DkMath.Analysis.DkReal) :
    ∀ n,
      (diffNonnegApprox x y n).lo ≤
          (diffNonnegApprox x y (n + 1)).lo ∧
        (diffNonnegApprox x y (n + 1)).hi ≤
          (diffNonnegApprox x y n).hi := by
  intro n
  constructor
  · apply max_le_max_left
    exact sub_le_sub (y.lo_le_succ_lo n) (x.succ_hi_le_hi n)
  · apply max_le_max_left
    exact sub_le_sub (y.succ_hi_le_hi n) (x.lo_le_succ_lo n)

/-- Widths of extracted Gap intervals tend to zero. -/
theorem tendsto_diffNonnegApprox_width_zero
    (x y : DkMath.Analysis.DkReal) :
    Filter.Tendsto (fun n => (diffNonnegApprox x y n).width)
      Filter.atTop (nhds 0) := by
  have hupper :
      Filter.Tendsto
        (fun n => (x.interval n).width + (y.interval n).width)
        Filter.atTop (nhds 0) := by
    simpa only [zero_add] using
      x.tendsto_width_zero.add y.tendsto_width_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun n => (diffNonnegApprox x y n).width_nonneg)
    (fun n => diffNonnegInterval_width_le (x.interval n) (y.interval n))

/-- Computable nonnegative Gap representation extracted from `x` and `y`. -/
def diffNonneg
    (x y : DkMath.Analysis.DkReal) : DkMath.Analysis.DkReal where
  interval := diffNonnegApprox x y
  nested := diffNonnegApprox_nested x y
  width_tends_zero := tendsto_diffNonnegApprox_width_zero x y

/-- The extracted Gap representation is stagewise nonnegative. -/
theorem nonnegative_diffNonneg
    (x y : DkMath.Analysis.DkReal) :
    Nonnegative (diffNonneg x y) := by
  intro n
  exact diffNonnegInterval_lo_nonneg (x.interval n) (y.interval n)

/-!
## II. Reconstruction of the Big universe
-/

/--
The separation between `x + diffNonneg x y` and `y` is bounded by the order
defect from `x` to `y` plus the two observation widths.
-/
theorem separation_add_diffNonneg_le
    (x y : DkMath.Analysis.DkReal) (n : ℕ) :
    ((add x (diffNonneg x y)).interval n).separation (y.interval n)
      ≤ orderDefect x y n +
        (x.interval n).width + (y.interval n).width := by
  simp only [add_interval, addApprox, diffNonneg, diffNonnegApprox,
    diffNonnegInterval, GapInterval.add_lo, GapInterval.add_hi,
    GapInterval.separation, orderDefect, GapInterval.width]
  have hxvalid := (x.interval n).le_lo_hi
  have hyvalid := (y.interval n).le_lo_hi
  have hrhs :
      0 ≤
        max 0 ((x.interval n).lo - (y.interval n).lo) +
          ((x.interval n).hi - (x.interval n).lo) +
          ((y.interval n).hi - (y.interval n).lo) :=
    add_nonneg
      (add_nonneg (le_max_left _ _) (sub_nonneg.mpr hxvalid))
      (sub_nonneg.mpr hyvalid)
  apply max_le
  · exact hrhs
  · apply max_le
    · by_cases hgap :
          (y.interval n).lo - (x.interval n).hi ≤ 0
      · rw [max_eq_left hgap]
        have hdef :
            (x.interval n).lo - (y.interval n).lo ≤
              max 0 ((x.interval n).lo - (y.interval n).lo) :=
          le_max_right _ _
        linarith
      · rw [max_eq_right (le_of_not_ge hgap)]
        linarith
    · have hmax :
          (y.interval n).hi - (x.interval n).lo ≤
            max 0 ((y.interval n).hi - (x.interval n).lo) :=
        le_max_right _ _
      linarith

/-- An ordered pair reconstructs its Big value by adding the extracted Gap. -/
theorem add_diffNonneg_equiv
    {x y : DkMath.Analysis.DkReal} (hxy : Le x y) :
    Equiv (add x (diffNonneg x y)) y := by
  have hupper :
      Filter.Tendsto
        (fun n =>
          orderDefect x y n +
            (x.interval n).width + (y.interval n).width)
        Filter.atTop (nhds 0) := by
    simpa only [zero_add, add_zero] using
      (hxy.add x.tendsto_width_zero).add y.tendsto_width_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun n =>
      ((add x (diffNonneg x y)).interval n).separation_nonneg
        (y.interval n))
    (separation_add_diffNonneg_le x y)

end DkMath.Analysis.DkReal

namespace DkMath.Analysis.DkNNReal

/-- The nonnegative Gap universe extracted from an ordered representative pair. -/
def diffOfLe (x y : DkNNReal) (_hxy : Le x y) : DkNNReal :=
  ⟨DkReal.diffNonneg x.val y.val,
    DkReal.nonnegative_diffNonneg x.val y.val⟩

/-- Adding the extracted Gap reconstructs the larger representative modulo equivalence. -/
theorem add_diffOfLe_equiv
    {x y : DkNNReal} (hxy : Le x y) :
    Equiv (add x (diffOfLe x y hxy)) y :=
  DkReal.add_diffNonneg_equiv hxy

end DkMath.Analysis.DkNNReal

namespace DkMath.Analysis.DkNNRealQ

/-!
## III. Canonical quotient order
-/

/-- Every ordered quotient pair admits a nonnegative additive Gap. -/
theorem exists_add_of_le
    {x y : DkNNRealQ} (hxy : x ≤ y) :
    ∃ z : DkNNRealQ, y = x + z := by
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro a b hab
  refine ⟨mk (DkNNReal.diffOfLe a b hab), ?_⟩
  exact Quotient.sound (DkNNReal.add_diffOfLe_equiv hab) |>.symm

/-- Existence of a nonnegative additive Gap implies order. -/
theorem le_of_exists_add
    {x y : DkNNRealQ} (h : ∃ z : DkNNRealQ, y = x + z) :
    x ≤ y := by
  obtain ⟨z, rfl⟩ := h
  calc
    x = x + 0 := (add_zero x).symm
    _ ≤ x + z := add_le_add_right (zero_le z) x

/-- Order is exactly the existence of a nonnegative Gap universe. -/
theorem le_iff_exists_add
    {x y : DkNNRealQ} :
    x ≤ y ↔ ∃ z : DkNNRealQ, y = x + z :=
  ⟨exists_add_of_le, le_of_exists_add⟩

/-- Mathlib interface for extracting an additive Gap from an order proof. -/
instance : ExistsAddOfLE DkNNRealQ where
  exists_add_of_le := exists_add_of_le

/--
Canonical additive order on the quotient.

This packages the DkMath statement that every ordered Big value is obtained by
filling its Body with a nonnegative Gap universe.
-/
instance : CanonicallyOrderedAdd DkNNRealQ where
  exists_add_of_le := exists_add_of_le
  le_add_self a b := by
    calc
      a = 0 + a := (zero_add a).symm
      _ ≤ b + a := add_le_add_left (zero_le b) a
  le_self_add a b := by
    calc
      a = a + 0 := (add_zero a).symm
      _ ≤ a + b := add_le_add_right (zero_le b) a

end DkMath.Analysis.DkNNRealQ
