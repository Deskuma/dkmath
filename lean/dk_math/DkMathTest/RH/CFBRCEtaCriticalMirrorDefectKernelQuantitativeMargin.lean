/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelQuantitativeMargin

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelQuantitativeMargin"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelQuantitativeMargin

open Filter
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspanOne : etaPairDerivativePhaseSpan s k ≤ 1)
    (hweight : 2 ≤ etaCriticalMirrorContinuousWeightR s x)
    (hsmall :
      2 * |s.im| *
          ((‖criticalMirror s‖ + ‖s‖) *
            etaCriticalMirrorContinuousWeightR s x) *
          etaPairDerivativePhaseSpan s k ≤
        (s.im ^ 2 / 4) *
          etaCriticalMirrorContinuousWeightR s x) :
    (s.im ^ 2 / 4) * etaCriticalMirrorContinuousWeightR s x ≤
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_ge_right_quarter_margin
    s k hleft hright hspanOne hweight hsmall

example
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspanOne : etaPairDerivativePhaseSpan s k ≤ 1)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2)
    (hsmall :
      2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
          etaPairDerivativePhaseSpan s k ≤
        s.im ^ 2 / 4) :
    s.im ^ 2 / 4 ≤
      -etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) :=
  neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_ge_left_quarter_margin
    s k hleft hright hspanOne hweight hsmall

example
    {s : ℂ} (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        (s.im ^ 2 / 4) * etaPairRadialDecay s x *
            etaCriticalMirrorContinuousWeightR s x ≤
          etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x) :=
  eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_right_quarter_margin_on_pair
    him hre

example
    {s : ℂ} (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        (s.im ^ 2 / 4) * etaPairRadialDecay s x ≤
          -etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x) :=
  eventually_neg_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_left_quarter_margin_on_pair
    him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelQuantitativeMargin
