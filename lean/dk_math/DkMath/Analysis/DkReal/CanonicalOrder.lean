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

/--
DkMath-facing name for the finite nonnegative Gap extracted inside a
Body--Big pair.

`diffNonnegInterval` remains the implementation name; this alias exposes the
construction as a Gap rather than as a subtraction operation.
-/
abbrev gapInterval (I J : GapInterval) : GapInterval :=
  diffNonnegInterval I J

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

/-- DkMath-facing name for the stagewise extracted Gap observations. -/
abbrev gapApprox
    (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
  diffNonnegApprox x y n

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

/-- DkMath-facing name for the extracted nonnegative Gap representation. -/
abbrev gap
    (x y : DkMath.Analysis.DkReal) : DkMath.Analysis.DkReal :=
  diffNonneg x y

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

/--
The nonnegative Gap universe filling `x` to `y`.

The order proof certifies that this extracted representation reconstructs the
same quotient Big as `y`.
-/
abbrev gapOfLe (x y : DkNNReal) (hxy : Le x y) : DkNNReal :=
  diffOfLe x y hxy

/-- Adding the extracted Gap reconstructs the larger representative modulo equivalence. -/
theorem add_diffOfLe_equiv
    {x y : DkNNReal} (hxy : Le x y) :
    Equiv (add x (diffOfLe x y hxy)) y :=
  DkReal.add_diffNonneg_equiv hxy

/--
The extracted canonical Gap is positive at stage `n` exactly when the Body
and Big representatives are strictly separated there.
-/
theorem gapOfLe_lo_pos_iff_leftSeparatedAt
    (x y : DkNNReal) (hxy : Le x y) (n : ℕ) :
    0 < ((gapOfLe x y hxy).val.interval n).lo ↔
      DkReal.LeftSeparatedAt x.val y.val n := by
  simp only [gapOfLe, diffOfLe, DkReal.diffNonneg,
    DkReal.diffNonnegApprox, DkReal.diffNonnegInterval,
    DkReal.LeftSeparatedAt]
  constructor
  · intro h
    by_contra hsep
    have hnonpos :
        (y.val.interval n).lo - (x.val.interval n).hi ≤ 0 :=
      sub_nonpos.mpr (le_of_not_gt hsep)
    rw [max_eq_left hnonpos] at h
    exact (lt_irrefl 0) h
  · intro hsep
    rw [max_eq_right (sub_nonneg.mpr hsep.le)]
    exact sub_pos.mpr hsep

/-- Strict wrapper order is finite positivity of the extracted canonical Gap. -/
theorem lt_iff_exists_gapOfLe_lo_pos
    (x y : DkNNReal) (hxy : Le x y) :
    Lt x y ↔ ∃ n, 0 < ((gapOfLe x y hxy).val.interval n).lo := by
  rw [lt_iff_exists_leftSeparatedAt]
  exact exists_congr fun n => (gapOfLe_lo_pos_iff_leftSeparatedAt x y hxy n).symm

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

/--
Multiplication by a strictly positive right factor preserves strict order.

For `x < y`, canonical order extracts `z` with `y = x + z`. The Gap cannot
be zero, hence `0 < z`; positivity of the factor gives `0 < z * a`. Strict
addition and distributivity then reconstruct the transformed strict Gap

`y * a = x * a + z * a`.
-/
theorem mul_lt_mul_of_pos_right
    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
    x * a < y * a := by
  obtain ⟨z, hz⟩ := exists_add_of_le (le_of_lt hxy)
  have hzpos : 0 < z := by
    rw [lt_iff_le_and_not_le]
    refine ⟨zero_le z, ?_⟩
    intro hzle
    have hz0 : z = 0 := le_antisymm hzle (zero_le z)
    subst z
    simp only [add_zero] at hz
    exact (ne_of_lt hxy) hz.symm
  have hza : 0 < z * a := zero_lt_mul hzpos ha
  calc
    x * a = x * a + 0 := (add_zero (x * a)).symm
    _ < x * a + z * a := add_lt_add_left hza (x * a)
    _ = (x + z) * a := (add_mul x z a).symm
    _ = y * a := congrArg (· * a) hz.symm

/-- Multiplication by a strictly positive left factor preserves strict order. -/
theorem mul_lt_mul_of_pos_left
    {x y a : DkNNRealQ} (hxy : x < y) (ha : 0 < a) :
    a * x < a * y := by
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hxy ha

/--
Order can be cancelled across a common left summand.

If the conclusion failed, totality would orient the operands strictly in the
opposite direction. Strict addition would then contradict the assumed
non-strict inequality.
-/
theorem le_of_add_le_add_left
    (a b c : DkNNRealQ) (h : a + b ≤ a + c) :
    b ≤ c := by
  rcases le_total b c with hbc | hcb
  · exact hbc
  · by_contra hnot
    have hlt : c < b := ⟨hcb, hnot⟩
    exact (not_lt_of_ge h) (add_lt_add_left hlt a)

/-- Order can be cancelled across a common right summand. -/
theorem le_of_add_le_add_right
    (a b c : DkNNRealQ) (h : b + a ≤ c + a) :
    b ≤ c := by
  rw [add_comm b a, add_comm c a] at h
  exact le_of_add_le_add_left a b c h

/-- Zero is strictly below one in the quotient order. -/
theorem zero_lt_one : (0 : DkNNRealQ) < 1 := by
  rw [show (0 : DkNNRealQ) = mk DkNNReal.zero by rfl,
    show (1 : DkNNRealQ) = mk DkNNReal.one by rfl,
    mk_lt_mk_iff, DkNNReal.zero_lt_iff_exists_lo_pos]
  exact ⟨0, by simp [DkNNReal.one, DkNNReal.ofRat]⟩

/--
Strict ordered-semiring compatibility for the quotient.

The interface requires only a semiring, partial order, cancellative ordered
addition, nontriviality, and strict multiplication by positive factors. It
does not install a `LinearOrder`, decidable comparison, or additive inverses.
-/
instance : IsStrictOrderedRing DkNNRealQ where
  add_le_add_left _ _ h z := add_le_add h (le_refl z)
  le_of_add_le_add_left := le_of_add_le_add_left
  zero_le_one := zero_le_one
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    exact mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right := by
    intro a ha b c hbc
    exact mul_lt_mul_of_pos_right hbc ha

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
