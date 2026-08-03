/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientProjection

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientProjection"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientProjection

open DkMath.RH.CFBRCProjection

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) =
      s.im ^ 2 *
        (etaCriticalMirrorContinuousWeightR s x - 1) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq s hx

example {s : ℂ} (him : s.im ≠ 0)
    (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    0 <
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_pos_of_half_lt_re
    him hre hx

example {s : ℂ} (him : s.im ≠ 0)
    (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) < 0 :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_neg_of_re_lt_half
    him hre hx

example (s : ℂ) (him : s.im ≠ 0)
    {x : ℝ} (hx : 1 < x) :
    (s.re < (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) < 0) ∨
    (s.re = (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) = 0) ∨
    ((1 : ℝ) / 2 < s.re ∧
      0 < etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_sign_trichotomy
    s him hx

example (s c r : ℂ) :
    |etaCriticalMirrorSignedVerticalProjection s (c * r) -
        etaCriticalMirrorSignedVerticalProjection s c| ≤
      |s.im| * ‖c‖ * ‖r - 1‖ :=
  abs_etaCriticalMirrorSignedVerticalProjection_mul_sub_le s c r

example (s : ℂ) (k : ℕ) (x : ℝ)
    (hphase : |etaPairResidualPhase s k x| ≤ 1) :
    ‖etaPairResidualRotation s k x - 1‖ ≤
      2 * |etaPairResidualPhase s k x| :=
  norm_etaPairResidualRotation_sub_one_le_two_mul_abs_phase
    s k x hphase

example (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspan : etaPairDerivativePhaseSpan s k ≤ 1) :
    |etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) -
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x)| ≤
      2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
        etaPairDerivativePhaseSpan s k :=
  abs_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_sub_le_phaseSpan
    s k hleft hright hspan

example {s c r : ℂ}
    (hbase : 0 < etaCriticalMirrorSignedVerticalProjection s c)
    (herr :
      |etaCriticalMirrorSignedVerticalProjection s (c * r) -
        etaCriticalMirrorSignedVerticalProjection s c| <
        etaCriticalMirrorSignedVerticalProjection s c) :
    0 < etaCriticalMirrorSignedVerticalProjection s (c * r) :=
  etaCriticalMirrorSignedVerticalProjection_mul_pos_of_rotation_error_lt
    hbase herr

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientProjection
