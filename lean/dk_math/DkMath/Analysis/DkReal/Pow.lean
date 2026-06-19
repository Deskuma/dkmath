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

The result is currently an interval sequence rather than a completed `DkReal`.
To construct the latter, a later checkpoint must prove that the powered widths
tend to zero, using suitable bounds on the exact `gapGN` factor.
-/

namespace DkMath.Analysis.DkReal

/-- A `DkReal` is nonnegative when every rational lower endpoint is nonnegative. -/
def Nonnegative (x : DkMath.Analysis.DkReal) : Prop :=
  ∀ n, 0 ≤ (x.interval n).lo

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

/--
Exact width formula for every powered approximation interval.

This identifies the remaining obligation for a full `DkReal` power map: prove
that this product tends to zero.
-/
theorem powNonnegApprox_width_eq
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonnegApprox d x hx n).width
      = (x.interval n).width *
        gapGN d (x.interval n).lo (x.interval n).width :=
  GapInterval.powNonneg_width_eq d (x.interval n) (hx n)

/-- Embedded nonnegative rationals satisfy the approximation nonnegativity condition. -/
theorem nonnegative_ofRat {q : ℚ} (hq : 0 ≤ q) :
    Nonnegative (DkMath.Analysis.DkReal.ofRat q) := by
  intro n
  simpa

end DkMath.Analysis.DkReal
