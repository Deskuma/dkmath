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

noncomputable section

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection

/-- Positive-real power kernel underlying every unsigned eta vector. -/
def etaRealKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s)

/-- Natural samples of the real kernel are exactly the unsigned eta vectors. -/
theorem etaRealKernel_nat
    (s : ℂ) (m : ℕ) :
    etaRealKernel s (((m + 1 : ℕ) : ℝ)) = etaUnsignedVector s m := by
  simp [etaRealKernel, etaUnsignedVector]

/--
The candidate derivative vector of `x ↦ x⁻ˢ` gains one full real decay power.
This norm identity is independent of the implementation chosen for the real
normed-space structure on `ℂ`.
-/
theorem norm_etaRealKernel_derivative
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(-s) * (x : ℂ) ^ (-s - 1)‖ =
      ‖s‖ * x ^ (-s.re - 1) := by
  rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

end DkMath.RH.Weave.Analytic
