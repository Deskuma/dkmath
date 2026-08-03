/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientEventualSign
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Positive radial size of the common eta-pair kernel on the positive axis. -/
noncomputable def etaPairRadialDecay
    (s : ℂ) (x : ℝ) : ℝ :=
  x ^ (-s.re - 1)

/-- The eta-pair radial decay is strictly positive on the positive axis. -/
theorem etaPairRadialDecay_pos
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    0 < etaPairRadialDecay s x := by
  unfold etaPairRadialDecay
  exact Real.rpow_pos_of_pos hx _

/--
After removing the phase at the pair-left endpoint, the common complex power
is a positive radial factor times the pair-local residual rotation.
-/
theorem etaPairBaseRotation_mul_cpow_eq_radial_mul_residual
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k * (x : ℂ) ^ (-s - 1) =
      ((etaPairRadialDecay s x : ℝ) : ℂ) *
        etaPairResidualRotation s k x := by
  have hx0 : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  unfold etaPairBaseRotation etaPairRadialDecay
  unfold etaPairResidualRotation etaPairResidualPhase
  rw [Complex.cpow_def_of_ne_zero hx0]
  rw [Real.rpow_def_of_pos hx]
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le]
  rw [← Complex.re_add_im s]
  push_cast
  ring

/--
The pair-left rotated defect kernel is the positive radial factor times the
already isolated coefficient-residual product.
-/
theorem etaPairBaseRotation_mul_defectPairIntegralKernel_factor
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k *
        etaCriticalMirrorDefectPairIntegralKernel s x =
      ((etaPairRadialDecay s x : ℝ) : ℂ) *
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) := by
  rw [etaCriticalMirrorDefectPairIntegralKernel_factor s hx]
  calc
    etaPairBaseRotation s k *
          (etaCriticalMirrorDefectCoefficient s x *
            (x : ℂ) ^ (-s - 1)) =
        etaCriticalMirrorDefectCoefficient s x *
          (etaPairBaseRotation s k * (x : ℂ) ^ (-s - 1)) := by
      ring
    _ = etaCriticalMirrorDefectCoefficient s x *
          (((etaPairRadialDecay s x : ℝ) : ℂ) *
            etaPairResidualRotation s k x) := by
      rw [etaPairBaseRotation_mul_cpow_eq_radial_mul_residual s k hx]
    _ = ((etaPairRadialDecay s x : ℝ) : ℂ) *
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) := by
      ring

/-- Signed vertical projection scales by the positive radial factor. -/
theorem etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x) =
      etaPairRadialDecay s x *
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) := by
  rw [etaPairBaseRotation_mul_defectPairIntegralKernel_factor s k hx]
  unfold etaCriticalMirrorSignedVerticalProjection
  simp
  ring

/--
Right of the critical line, every sufficiently late pair has positive signed
vertical projection for the actual defect integral kernel in its own frame.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_pos_on_pair
    {s : ℂ} (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        0 < etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x) := by
  filter_upwards
    [eventually_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_pos_on_pair
      him hre] with k hk
  intro x hleft hright
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel
    s k hx]
  exact mul_pos (etaPairRadialDecay_pos s hx) (hk x hleft hright)

/--
Left of the critical line, every sufficiently late pair has negative signed
vertical projection for the actual defect integral kernel in its own frame.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_neg_on_pair
    {s : ℂ} (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x) < 0 := by
  filter_upwards
    [eventually_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_neg_on_pair
      him hre] with k hk
  intro x hleft hright
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel
    s k hx]
  exact mul_neg_of_pos_of_neg
    (etaPairRadialDecay_pos s hx) (hk x hleft hright)

end DkMath.RH.CFBRCProjection
