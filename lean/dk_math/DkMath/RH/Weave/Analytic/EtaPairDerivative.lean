/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaTermDecay
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairDerivative"

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection

/-- Positive-real power kernel underlying every unsigned eta vector. -/
noncomputable def etaRealKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s)

/-- Natural samples of the real kernel are exactly the unsigned eta vectors. -/
theorem etaRealKernel_nat
    (s : ℂ) (m : ℕ) :
    etaRealKernel s (((m + 1 : ℕ) : ℝ)) = etaUnsignedVector s m := by
  simp [etaRealKernel, etaUnsignedVector]

/--
Away from the origin, the real-variable derivative of `x ↦ x⁻ˢ` is
`-s * x⁻ˢ⁻¹`.
-/
theorem hasDerivAt_etaRealKernel
    {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (etaRealKernel s)
      ((-s) * (x : ℂ) ^ (-s - 1)) x := by
  simpa [etaRealKernel] using
    (hasDerivAt_ofReal_cpow_const (x := x) hx (r := -s) (neg_ne_zero.mpr hs))

/-- The derivative norm depends only on `re s` and gains one decay power. -/
theorem norm_etaRealKernel_derivative
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(-s) * (x : ℂ) ^ (-s - 1)‖ =
      ‖s‖ * x ^ (-s.re - 1) := by
  rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Explicit norm formula for the derivative of the eta real kernel. -/
theorem norm_deriv_etaRealKernel
    {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    ‖deriv (etaRealKernel s) x‖ =
      ‖s‖ * x ^ (-s.re - 1) := by
  rw [(hasDerivAt_etaRealKernel hs hx.ne').deriv]
  exact norm_etaRealKernel_derivative s hx

end DkMath.RH.Weave.Analytic
