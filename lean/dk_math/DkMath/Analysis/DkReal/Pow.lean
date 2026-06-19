/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Basic

#print "file: DkMath.Analysis.DkReal.Pow"

/-!
# Nonnegative power approximations for DkReal

This file lifts `GapInterval.powNonneg` pointwise to the approximation sequence
of a nonnegative `DkReal`.

It separates the finite interval transformation from the convergence theorem.
`powNonnegApprox` supplies the rational observations and proves nestedness.
`DkMath.Analysis.DkReal.PowBound` proves uniform boundedness of the exact
`gapGN` factor and packages these observations as the completed `powNonneg`
operation.

Mathematically, this file isolates the identity

`width(I^d) = width(I) * gapGN d I.lo width(I)`

before any limiting argument is applied.
-/

namespace DkMath.Analysis.DkReal

/-- A `DkReal` is nonnegative when every rational lower endpoint is nonnegative. -/
def Nonnegative (x : DkMath.Analysis.DkReal) : Prop :=
  ∀ n, 0 ≤ (x.interval n).lo

/-- Nonnegativity of the initial lower endpoint propagates to every stage. -/
theorem nonnegative_of_initial_lo
    (x : DkMath.Analysis.DkReal) (h0 : 0 ≤ (x.interval 0).lo) :
    Nonnegative x := by
  intro n
  exact h0.trans (x.lo_mono (Nat.zero_le n))

/--
Apply the natural power map to every approximation interval of a nonnegative
`DkReal`.

This definition is computational: it only transforms rational endpoints.
-/
def powNonnegApprox
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    ℕ → GapInterval :=
  fun n => (x.interval n).powNonneg d (hx n)

/-- Lower endpoint of a powered approximation interval. -/
@[simp]
theorem powNonnegApprox_lo
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonnegApprox d x hx n).lo = (x.interval n).lo ^ d := rfl

/-- Upper endpoint of a powered approximation interval. -/
@[simp]
theorem powNonnegApprox_hi
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonnegApprox d x hx n).hi = (x.interval n).hi ^ d := rfl

/-- Powered lower endpoints remain monotone between consecutive stages. -/
theorem powNonnegApprox_lo_le_succ_lo
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonnegApprox d x hx n).lo
      ≤ (powNonnegApprox d x hx (n + 1)).lo := by
  exact pow_le_pow_left₀ (hx n) (x.lo_le_succ_lo n) d

/-- Powered upper endpoints remain antitone between consecutive stages. -/
theorem powNonnegApprox_succ_hi_le_hi
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonnegApprox d x hx (n + 1)).hi
      ≤ (powNonnegApprox d x hx n).hi := by
  have hnext : 0 ≤ (x.interval (n + 1)).hi :=
    (hx (n + 1)).trans (x.interval (n + 1)).le_lo_hi
  exact pow_le_pow_left₀ hnext (x.succ_hi_le_hi n) d

/-- The pointwise powered interval sequence is nested. -/
theorem powNonnegApprox_nested
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    ∀ n,
      (powNonnegApprox d x hx n).lo
          ≤ (powNonnegApprox d x hx (n + 1)).lo ∧
        (powNonnegApprox d x hx (n + 1)).hi
          ≤ (powNonnegApprox d x hx n).hi := by
  intro n
  exact ⟨powNonnegApprox_lo_le_succ_lo d x hx n,
    powNonnegApprox_succ_hi_le_hi d x hx n⟩

/-- Every powered approximation interval has nonnegative width. -/
theorem powNonnegApprox_width_nonneg
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    0 ≤ (powNonnegApprox d x hx n).width :=
  (powNonnegApprox d x hx n).width_nonneg

/-- Powered approximation intervals satisfy arbitrary-stage containment. -/
theorem powNonnegApprox_interval_subset_of_le
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    {n m : ℕ} (h : n ≤ m) :
    Set.Icc (powNonnegApprox d x hx m).lo (powNonnegApprox d x hx m).hi
      ⊆ Set.Icc (powNonnegApprox d x hx n).lo
        (powNonnegApprox d x hx n).hi := by
  intro q hq
  constructor
  · exact
      (pow_le_pow_left₀ (hx n) (x.lo_mono h) d).trans hq.1
  · have hmhi : 0 ≤ (x.interval m).hi :=
      (hx m).trans (x.interval m).le_lo_hi
    exact hq.2.trans (pow_le_pow_left₀ hmhi (x.hi_antitone h) d)

/--
Exact width formula for every powered approximation interval.

This identifies the convergence obligation discharged in `PowBound`: the
first factor tends to zero and the exact correction-kernel factor is uniformly
bounded on a fixed nonnegative rational box.
-/
theorem powNonnegApprox_width_eq
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonnegApprox d x hx n).width
      = (x.interval n).width *
        gapGN d (x.interval n).lo (x.interval n).width :=
  GapInterval.powNonneg_width_eq d (x.interval n) (hx n)

/--
If the exact `gapGN` factors along a nonnegative approximation are bounded,
then the powered interval widths tend to zero.
-/
theorem tendsto_powNonnegApprox_width_zero_of_gapGN_bounded
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    (hbounded :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (norm ∘ fun n =>
          gapGN d (x.interval n).lo (x.interval n).width)) :
    Filter.Tendsto (fun n => (powNonnegApprox d x hx n).width)
      Filter.atTop (nhds 0) := by
  have hmul :
      Filter.Tendsto
        (fun n =>
          (x.interval n).width *
            gapGN d (x.interval n).lo (x.interval n).width)
        Filter.atTop (nhds 0) :=
    x.tendsto_width_zero.zero_mul_isBoundedUnder_le hbounded
  simpa only [powNonnegApprox_width_eq] using hmul

/--
Construct the full powered `DkReal` once boundedness of the exact correction
kernel has been supplied.

This conditional constructor records the interface between finite rational
computation and the bounded-times-null convergence principle. The canonical
unconditional operation is `powNonneg` in `PowBound`.
-/
def powNonnegOfGapGNBounded
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    (hbounded :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (norm ∘ fun n =>
          gapGN d (x.interval n).lo (x.interval n).width)) :
    DkMath.Analysis.DkReal where
  interval := powNonnegApprox d x hx
  nested := powNonnegApprox_nested d x hx
  width_tends_zero :=
    tendsto_powNonnegApprox_width_zero_of_gapGN_bounded d x hx hbounded

/-- The intervals of the conditionally completed power map are the powered approximations. -/
@[simp]
theorem powNonnegOfGapGNBounded_interval
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    (hbounded :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (norm ∘ fun n =>
          gapGN d (x.interval n).lo (x.interval n).width))
    (n : ℕ) :
    (powNonnegOfGapGNBounded d x hx hbounded).interval n
      = powNonnegApprox d x hx n := rfl

/-- Embedded nonnegative rationals satisfy the approximation nonnegativity condition. -/
theorem nonnegative_ofRat {q : ℚ} (hq : 0 ≤ q) :
    Nonnegative (DkMath.Analysis.DkReal.ofRat q) := by
  intro n
  simpa

end DkMath.Analysis.DkReal
