/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.SquareTailGapIdentity
import DkMath.ABC.GNValuationExcess

#print "file: DkMath.ABC.ABCEpsilonIdentity"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Intrinsic ABC epsilon identities

This module identifies the multiplicity discarded by `rad` with the exact
square-tail quotient.  It is the first bridge from the existing GN valuation
accounting to the intrinsic epsilon coordinate of an ABC triple.
-/

namespace DkMath.ABC

/--
The logarithmic valuation multiplicity beyond radical support is exactly the
logarithm of the square-tail quotient.
-/
theorem valuationExcess_eq_log_sqTail
    {m : ℕ} (hm : m ≠ 0) :
    valuationExcess m = Real.log (sqTail m : ℝ) := by
  have hlog := log_eq_log_rad_add_valuationExcess hm
  have hdecomp := nat_eq_sqTail_mul_rad_real m hm
  have hsqTail : (sqTail m : ℝ) ≠ 0 := by
    intro hzero
    have hsqTailNat : sqTail m = 0 := by
      exact_mod_cast hzero
    apply hm
    calc
      m = sqTail m * rad m := nat_eq_sqTail_mul_rad m hm
      _ = 0 := by simp [hsqTailNat]
  have hrad : (rad m : ℝ) ≠ 0 := by
    exact_mod_cast rad_ne_zero m
  have hmul :
      Real.log (m : ℝ) =
        Real.log (sqTail m : ℝ) + Real.log (rad m : ℝ) := by
    rw [hdecomp, Real.log_mul hsqTail hrad]
  linarith

/--
The square-tail debt of an ABC triple is exactly its output valuation excess
minus the logarithmic radical support already paid by the two inputs.
-/
theorem Triple.squareTailDebt_eq_valuationExcess_sub_log_rad_ab
    (T : Triple)
    (hc : T.c ≠ 0) :
    T.squareTailDebt =
      valuationExcess T.c - Real.log (rad (T.a * T.b) : ℝ) := by
  simpa [Triple.squareTailDebt] using congrArg
    (fun x : ℝ => x - Real.log (rad (T.a * T.b) : ℝ))
    (valuationExcess_eq_log_sqTail hc).symm

end DkMath.ABC
