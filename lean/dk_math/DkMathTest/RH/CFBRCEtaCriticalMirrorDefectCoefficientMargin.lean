/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientMargin

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientMargin"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientMargin

open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖etaCriticalMirrorContinuousWeight s x‖ =
      etaCriticalMirrorContinuousWeightR s x :=
  norm_etaCriticalMirrorContinuousWeight s hx

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
      ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x +
        ‖s‖ :=
  norm_etaCriticalMirrorDefectCoefficient_le_transport s hx

example (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : 1 ≤ etaCriticalMirrorContinuousWeightR s x) :
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
      (‖criticalMirror s‖ + ‖s‖) *
        etaCriticalMirrorContinuousWeightR s x :=
  norm_etaCriticalMirrorDefectCoefficient_le_right_linear s hx hweight

example (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ 1) :
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
      ‖criticalMirror s‖ + ‖s‖ :=
  norm_etaCriticalMirrorDefectCoefficient_le_left_bounded s hx hweight

example (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : 2 ≤ etaCriticalMirrorContinuousWeightR s x) :
    (s.im ^ 2 / 2) * etaCriticalMirrorContinuousWeightR s x ≤
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_right_margin
    s hx hweight

example (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2) :
    s.im ^ 2 / 2 ≤
      -etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) :=
  neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_left_margin
    s hx hweight

example (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspanOne : etaPairDerivativePhaseSpan s k ≤ 1)
    (hweight : 2 ≤ etaCriticalMirrorContinuousWeightR s x)
    (hsmall :
      2 * |s.im| *
          ((‖criticalMirror s‖ + ‖s‖) *
            etaCriticalMirrorContinuousWeightR s x) *
          etaPairDerivativePhaseSpan s k <
        (s.im ^ 2 / 2) *
          etaCriticalMirrorContinuousWeightR s x) :
    0 < etaCriticalMirrorSignedVerticalProjection s
      (etaCriticalMirrorDefectCoefficient s x *
        etaPairResidualRotation s k x) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_pos_of_right_margin
    s k hleft hright hspanOne hweight hsmall

example (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspanOne : etaPairDerivativePhaseSpan s k ≤ 1)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2)
    (hsmall :
      2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
          etaPairDerivativePhaseSpan s k <
        s.im ^ 2 / 2) :
    etaCriticalMirrorSignedVerticalProjection s
      (etaCriticalMirrorDefectCoefficient s x *
        etaPairResidualRotation s k x) < 0 :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_neg_of_left_margin
    s k hleft hright hspanOne hweight hsmall

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientMargin
