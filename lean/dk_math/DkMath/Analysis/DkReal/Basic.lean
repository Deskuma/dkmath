/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Interval

#print "file: DkMath.Analysis.DkReal.Basic"

/-!
# Nested rational interval reals

This file defines the first `DkReal` carrier. A value is represented by nested
rational gap intervals whose widths converge to zero.

No evaluation into Mathlib's real numbers is chosen here. This keeps the
computational approximation structure separate from its future semantic bridge.

The carrier is a representation space rather than an extensional real-number
type: distinct interval sequences may encode the same limiting value.
Extensional identification is supplied later by `DkReal.Equiv`.
-/

namespace DkMath.Analysis

/--
A DkMath real approximation given by nested rational intervals with vanishing
width.

The interval at `n + 1` is contained in the interval at `n`. The convergence
condition says that the remaining rational uncertainty tends to zero. This is
the nested-interval analogue of a regular Cauchy representation, with explicit
lower and upper rational observations rather than a chosen real limit.

No completeness axiom is stored in this structure. Completeness enters only
when a semantic value in Mathlib's `Real` is later extracted.
-/
structure DkReal where
  interval : ℕ → DkReal.GapInterval
  nested : ∀ n,
    (interval n).lo ≤ (interval (n + 1)).lo ∧
      (interval (n + 1)).hi ≤ (interval n).hi
  width_tends_zero :
    Filter.Tendsto (fun n => (interval n).width) Filter.atTop (nhds 0)

namespace DkReal

/-- The lower endpoint does not decrease at the next approximation stage. -/
theorem lo_le_succ_lo (x : DkReal) (n : ℕ) :
    (x.interval n).lo ≤ (x.interval (n + 1)).lo :=
  (x.nested n).1

/-- The upper endpoint does not increase at the next approximation stage. -/
theorem succ_hi_le_hi (x : DkReal) (n : ℕ) :
    (x.interval (n + 1)).hi ≤ (x.interval n).hi :=
  (x.nested n).2

/--
Lower endpoints are monotone across arbitrary approximation stages.

This is one half of persistence for comparison orientation: a later Core
observation cannot move left of an earlier lower bound.
-/
theorem lo_mono (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    (x.interval n).lo ≤ (x.interval m).lo := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih => exact ih.trans (x.lo_le_succ_lo m)

/--
Upper endpoints are antitone across arbitrary approximation stages.

Together with `lo_mono`, this implies that once two approximation intervals
are strictly separated, their left/right orientation persists at every later
stage.
-/
theorem hi_antitone (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    (x.interval m).hi ≤ (x.interval n).hi := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih => exact (x.succ_hi_le_hi m).trans ih

/-- Every approximation interval has nonnegative rational width. -/
theorem width_nonneg (x : DkReal) (n : ℕ) :
    0 ≤ (x.interval n).width :=
  (x.interval n).width_nonneg

/-- Nested approximation makes interval width nonincreasing at each step. -/
theorem width_succ_le_width (x : DkReal) (n : ℕ) :
    (x.interval (n + 1)).width ≤ (x.interval n).width := by
  exact sub_le_sub (x.succ_hi_le_hi n) (x.lo_le_succ_lo n)

/-- Later approximation intervals are contained in the preceding interval. -/
theorem interval_succ_subset (x : DkReal) (n : ℕ) :
    Set.Icc (x.interval (n + 1)).lo (x.interval (n + 1)).hi
      ⊆ Set.Icc (x.interval n).lo (x.interval n).hi := by
  intro q hq
  exact ⟨(x.lo_le_succ_lo n).trans hq.1, hq.2.trans (x.succ_hi_le_hi n)⟩

/-- Every later approximation interval is contained in every earlier one. -/
theorem interval_subset_of_le (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    Set.Icc (x.interval m).lo (x.interval m).hi
      ⊆ Set.Icc (x.interval n).lo (x.interval n).hi := by
  intro q hq
  exact ⟨(x.lo_mono h).trans hq.1, hq.2.trans (x.hi_antitone h)⟩

/-- The interval widths of a `DkReal` tend to zero by construction. -/
theorem tendsto_width_zero (x : DkReal) :
    Filter.Tendsto (fun n => (x.interval n).width) Filter.atTop (nhds 0) :=
  x.width_tends_zero

/-- Embed a rational number as the constant sequence of singleton intervals. -/
def ofRat (q : ℚ) : DkReal where
  interval _ := GapInterval.singleton q
  nested := by
    intro n
    simp
  width_tends_zero := by
    simp

/-- Every approximation interval of an embedded rational is its singleton. -/
@[simp]
theorem ofRat_interval (q : ℚ) (n : ℕ) :
    (ofRat q).interval n = GapInterval.singleton q := rfl

/-- Embedded rationals have zero approximation width at every stage. -/
@[simp]
theorem ofRat_width (q : ℚ) (n : ℕ) :
    ((ofRat q).interval n).width = 0 := by
  simp

end DkReal

end DkMath.Analysis
