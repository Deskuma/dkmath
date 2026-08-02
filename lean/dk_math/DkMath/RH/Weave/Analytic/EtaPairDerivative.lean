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

/--
Mean-value bound for the eta real kernel on a positive interval.  The public
statement contains only norms and is therefore independent of the chosen
`NormedSpace ℝ ℂ` implementation.
-/
theorem norm_etaRealKernel_sub_le
    {s : ℂ} (hre : 0 < s.re) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ‖etaRealKernel s b - etaRealKernel s a‖ ≤
      (‖s‖ * a ^ (-s.re - 1)) * (b - a) := by
  letI : NormedSpace ℝ ℂ := NormedSpace.complexToReal
  have hs : s ≠ 0 := by
    intro hs0
    simpa [hs0] using hre
  have hExp : -s.re - 1 ≤ 0 := by linarith
  have hderiv :
      ∀ x ∈ Set.Icc a b,
        HasDerivWithinAt (etaRealKernel s)
          ((-s) * (x : ℂ) ^ (-s - 1)) (Set.Icc a b) x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    simpa [etaRealKernel] using
      (hasDerivAt_ofReal_cpow_const
        (x := x) hxpos.ne' (r := -s) (neg_ne_zero.mpr hs)).hasDerivWithinAt
  have hbound :
      ∀ x ∈ Set.Ico a b,
        ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤
          ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    rw [norm_etaRealKernel_derivative s hxpos]
    gcongr
    exact
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hExp
        ha hxpos hx.1
  exact
    norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbound b ⟨hab, le_rfl⟩

/--
Each paired eta difference gains one full decay power compared with an
individual unsigned eta term.
-/
theorem norm_etaPairTerm_le
    {s : ℂ} (hre : 0 < s.re) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤
      ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
  have ha : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  have hab :
      (((2 * k + 1 : ℕ) : ℝ)) ≤ (((2 * k + 2 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have h := norm_etaRealKernel_sub_le hre ha hab
  have hA :
      etaRealKernel s (((2 * k + 1 : ℕ) : ℝ)) =
        etaUnsignedVector s (2 * k) := by
    simpa using etaRealKernel_nat s (2 * k)
  have hB :
      etaRealKernel s (((2 * k + 2 : ℕ) : ℝ)) =
        etaUnsignedVector s (2 * k + 1) := by
    simpa [Nat.add_assoc] using etaRealKernel_nat s (2 * k + 1)
  rw [hA, hB] at h
  simpa [etaPairTerm, norm_neg, sub_eq_add_neg, add_comm] using h

end DkMath.RH.Weave.Analytic
