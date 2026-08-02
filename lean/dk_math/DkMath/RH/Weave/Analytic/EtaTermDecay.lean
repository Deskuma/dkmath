/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairedLimit
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaTermDecay"

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection

/-- The unsigned eta vector is the reciprocal positive-base complex power. -/
theorem etaUnsignedVector_eq_one_div_cpow
    (s : ℂ) (m : ℕ) :
    etaUnsignedVector s m = 1 / (((m + 1 : ℕ) : ℂ) ^ s) := by
  rw [etaUnsignedVector, Complex.cpow_neg]
  rfl

/--
The norm of an unsigned eta vector depends only on the real part of `s`.
The imaginary coordinate remains in the complex phase and disappears only
under the norm projection.
-/
theorem norm_etaUnsignedVector
    (s : ℂ) (m : ℕ) :
    ‖etaUnsignedVector s m‖ =
      ((m + 1 : ℕ) : ℝ) ^ (-s.re) := by
  rw [etaUnsignedVector]
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos]
  · simp
  · exact_mod_cast Nat.succ_pos m

/-- Alternating signs do not change the magnitude of an eta vector. -/
theorem norm_etaSignedVector
    (s : ℂ) (m : ℕ) :
    ‖etaSignedVector s m‖ = ‖etaUnsignedVector s m‖ := by
  by_cases hm : Even m <;> simp [etaSignedVector, hm]

/-- Explicit real-decay formula for every signed eta vector. -/
theorem norm_etaSignedVector_eq_rpow
    (s : ℂ) (m : ℕ) :
    ‖etaSignedVector s m‖ =
      ((m + 1 : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_etaSignedVector, norm_etaUnsignedVector]

/-- The paired eta difference obeys the elementary triangle bound. -/
theorem norm_etaPairTerm_le
    (s : ℂ) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤
      ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re) +
        ((2 * k + 2 : ℕ) : ℝ) ^ (-s.re) := by
  unfold etaPairTerm
  calc
    ‖etaUnsignedVector s (2 * k) - etaUnsignedVector s (2 * k + 1)‖ ≤
        ‖etaUnsignedVector s (2 * k)‖ +
          ‖etaUnsignedVector s (2 * k + 1)‖ := norm_sub_le _ _
    _ = ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re) +
          ((2 * k + 2 : ℕ) : ℝ) ^ (-s.re) := by
      rw [norm_etaUnsignedVector, norm_etaUnsignedVector]
      congr 2 <;> omega

end DkMath.RH.Weave.Analytic
