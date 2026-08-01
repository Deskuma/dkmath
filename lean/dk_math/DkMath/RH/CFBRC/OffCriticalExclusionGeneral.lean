/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.OffCriticalExclusion
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.OffCriticalExclusionGeneral"

namespace DkMath.RH.CFBRCProjection

open DkMath.CFBRC.TrigBridge

/--
The standard CFBRC polynomial has no real-input zero away from `X = 0`
for any positive degree.

The proof is independent of zeta.  From

`(X + iΘ)^d = (iΘ)^d`

we compare complex norms, cancel the positive natural power on the
nonnegative reals, and then compare norm squares.  The remaining real
identity is `X^2 + Θ^2 = Θ^2`, hence `X = 0`.
-/
theorem cfbrcR_eq_zero_iff_x_eq_zero
    {d : ℕ} (hd : 0 < d) (X Θ : ℝ) :
    cfbrcR d X Θ = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hp :
        (((X : ℂ) + Complex.I * (Θ : ℂ)) ^ d) =
          ((Complex.I * (Θ : ℂ)) ^ d) := by
      have h' :
          (((X : ℂ) + Complex.I * (Θ : ℂ)) ^ d) -
              ((Complex.I * (Θ : ℂ)) ^ d) = 0 := by
        simpa [cfbrcR, cfbrc] using h
      exact sub_eq_zero.mp h'

    have hnormPow :
        ‖(X : ℂ) + Complex.I * (Θ : ℂ)‖ ^ d =
          ‖Complex.I * (Θ : ℂ)‖ ^ d := by
      have hnorm := congrArg (fun z : ℂ => ‖z‖) hp
      simpa only [Complex.norm_pow] using hnorm

    have hnorm :
        ‖(X : ℂ) + Complex.I * (Θ : ℂ)‖ =
          ‖Complex.I * (Θ : ℂ)‖ := by
      exact
        (pow_left_inj₀
          (Complex.norm_nonneg _)
          (Complex.norm_nonneg _)
          (Nat.ne_of_gt hd)).mp hnormPow

    have hnormSq :
        Complex.normSq ((X : ℂ) + Complex.I * (Θ : ℂ)) =
          Complex.normSq (Complex.I * (Θ : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hnorm]

    have hsq : X ^ 2 + Θ ^ 2 = Θ ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using hnormSq

    nlinarith
  · intro hX
    subst X
    exact cfbrcR_x_zero d Θ

/--
For every positive degree, the centered standard CFBRC projection closes
exactly on `σ = 1 / 2`.
-/
theorem offCriticalCFBRC_eq_zero_iff_re_eq_half
    {d : ℕ} (hd : 0 < d) (σ Θ : ℝ) :
    offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2 := by
  rw [offCriticalCFBRC, cfbrcR_eq_zero_iff_x_eq_zero hd,
    centeredSigma_eq_zero_iff]

/--
General positive-degree zero-preserving bridge.

The future analytic realization must provide `map_zero`; no critical-line
statement is included in this structure.
-/
structure ZeroToCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s → offCriticalCFBRC d s.re (phase s) = 0

/--
Any selected complex zero mapped to a positive-degree standard CFBRC zero
has real part `1 / 2`.
-/
theorem re_eq_half_of_zeroToCFBRCBridge
    {Zero : ℂ → Prop}
    (bridge : ZeroToCFBRCBridge Zero)
    {s : ℂ}
    (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact
    (offCriticalCFBRC_eq_zero_iff_re_eq_half
      bridge.hd s.re (bridge.phase s)).mp
      (bridge.map_zero hs)

end DkMath.RH.CFBRCProjection
