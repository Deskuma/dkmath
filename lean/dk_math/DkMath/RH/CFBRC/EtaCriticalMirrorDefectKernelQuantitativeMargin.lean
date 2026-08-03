/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockProjection
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelQuantitativeMargin"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/--
At a nonreal point, the pair-local residual-rotation error is eventually at
most one quarter of the fixed vertical coefficient margin.
-/
private theorem eventually_defectCoefficient_rotation_factor_le_quarter_vertical_margin
    (s : ℂ) (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
          etaPairDerivativePhaseSpan s k ≤
        s.im ^ 2 / 4 := by
  have hmargin : 0 < s.im ^ 2 / 4 := by
    positivity
  have hlim :
      Tendsto
        (fun k : ℕ =>
          (2 * |s.im| * (‖criticalMirror s‖ + ‖s‖)) *
            etaPairDerivativePhaseSpan s k)
        atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.const_mul
        (2 * |s.im| * (‖criticalMirror s‖ + ‖s‖))
        (etaPairDerivativePhaseSpan_tendsto_zero s))
  filter_upwards [hlim.eventually_lt_const hmargin] with k hk
  simpa [mul_assoc] using hk.le

/--
On the growing-weight side, one quarter of the explicit coefficient margin
survives the pair-local residual rotation.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_ge_right_quarter_margin
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
          etaPairResidualRotation s k x) := by
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  have hnorm :
      ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
        (‖criticalMirror s‖ + ‖s‖) *
          etaCriticalMirrorContinuousWeightR s x :=
    norm_etaCriticalMirrorDefectCoefficient_le_right_linear
      s hx (le_trans (by norm_num) hweight)
  have herror :
      |etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) -
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)| ≤
        2 * |s.im| *
          ((‖criticalMirror s‖ + ‖s‖) *
            etaCriticalMirrorContinuousWeightR s x) *
          etaPairDerivativePhaseSpan s k := by
    calc
      |etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) -
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)| ≤
          2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
            etaPairDerivativePhaseSpan s k :=
        abs_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_sub_le_phaseSpan
          s k hleft hright hspanOne
      _ ≤
          2 * |s.im| *
            ((‖criticalMirror s‖ + ‖s‖) *
              etaCriticalMirrorContinuousWeightR s x) *
            etaPairDerivativePhaseSpan s k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnorm (by positivity))
          (etaPairDerivativePhaseSpan_nonneg s k)
  have hbase :=
    etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_right_margin
      s hx hweight
  have hbaseTwo :
      2 * ((s.im ^ 2 / 4) * etaCriticalMirrorContinuousWeightR s x) ≤
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) := by
    calc
      2 * ((s.im ^ 2 / 4) * etaCriticalMirrorContinuousWeightR s x) =
          (s.im ^ 2 / 2) * etaCriticalMirrorContinuousWeightR s x := by
        ring
      _ ≤ etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) := hbase
  have hdiffLower := (abs_le.mp herror).1
  linarith

/--
On the decaying-weight side, one quarter of the fixed negative coefficient
margin survives the pair-local residual rotation.
-/
theorem neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_ge_left_quarter_margin
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
          etaPairResidualRotation s k x) := by
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  have hnorm :
      ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
        ‖criticalMirror s‖ + ‖s‖ :=
    norm_etaCriticalMirrorDefectCoefficient_le_left_bounded
      s hx (hweight.trans (by norm_num))
  have herror :
      |etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) -
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)| ≤
        2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
          etaPairDerivativePhaseSpan s k := by
    calc
      |etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) -
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)| ≤
          2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
            etaPairDerivativePhaseSpan s k :=
        abs_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_sub_le_phaseSpan
          s k hleft hright hspanOne
      _ ≤
          2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
            etaPairDerivativePhaseSpan s k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnorm (by positivity))
          (etaPairDerivativePhaseSpan_nonneg s k)
  have hbase :=
    neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_left_margin
      s hx hweight
  have hbaseTwo :
      2 * (s.im ^ 2 / 4) ≤
        -etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) := by
    calc
      2 * (s.im ^ 2 / 4) = s.im ^ 2 / 2 := by ring
      _ ≤ -etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) := hbase
  have hdiffUpper := (abs_le.mp herror).2
  linarith

/--
Right of the critical line, the rotated defect kernel carries an explicit
positive pointwise margin.
-/
theorem etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_right_quarter_margin
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
    (s.im ^ 2 / 4) * etaPairRadialDecay s x *
        etaCriticalMirrorContinuousWeightR s x ≤
      etaCriticalMirrorSignedVerticalProjection s
        (etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x) := by
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel
    s k hx]
  have hcoeff :=
    etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_ge_right_quarter_margin
      s k hleft hright hspanOne hweight hsmall
  calc
    (s.im ^ 2 / 4) * etaPairRadialDecay s x *
        etaCriticalMirrorContinuousWeightR s x =
      etaPairRadialDecay s x *
        ((s.im ^ 2 / 4) * etaCriticalMirrorContinuousWeightR s x) := by
      ring
    _ ≤ etaPairRadialDecay s x *
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) :=
      mul_le_mul_of_nonneg_left hcoeff
        (etaPairRadialDecay_pos s hx).le

/--
Left of the critical line, the rotated defect kernel carries an explicit
negative pointwise margin.
-/
theorem neg_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_left_quarter_margin
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspanOne : etaPairDerivativePhaseSpan s k ≤ 1)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2)
    (hsmall :
      2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
          etaPairDerivativePhaseSpan s k ≤
        s.im ^ 2 / 4) :
    (s.im ^ 2 / 4) * etaPairRadialDecay s x ≤
      -etaCriticalMirrorSignedVerticalProjection s
        (etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x) := by
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel
    s k hx]
  have hcoeff :=
    neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_ge_left_quarter_margin
      s k hleft hright hspanOne hweight hsmall
  calc
    (s.im ^ 2 / 4) * etaPairRadialDecay s x =
      etaPairRadialDecay s x * (s.im ^ 2 / 4) := by ring
    _ ≤ etaPairRadialDecay s x *
        (-etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x)) :=
      mul_le_mul_of_nonneg_left hcoeff
        (etaPairRadialDecay_pos s hx).le
    _ = -
        (etaPairRadialDecay s x *
          etaCriticalMirrorSignedVerticalProjection s
            (etaCriticalMirrorDefectCoefficient s x *
              etaPairResidualRotation s k x)) := by ring

/--
Right of the critical line, the explicit positive pointwise kernel margin
holds throughout every sufficiently late eta-pair interval.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_right_quarter_margin_on_pair
    {s : ℂ} (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        (s.im ^ 2 / 4) * etaPairRadialDecay s x *
            etaCriticalMirrorContinuousWeightR s x ≤
          etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x) := by
  have hthreshold :=
    eventually_two_le_etaCriticalMirrorContinuousWeightR_on_pair_of_half_lt_re
      hre
  have hsmall :=
    eventually_defectCoefficient_rotation_factor_le_quarter_vertical_margin
      s him
  have hspan :
      ∀ᶠ k : ℕ in atTop,
        etaPairDerivativePhaseSpan s k < 1 :=
    (etaPairDerivativePhaseSpan_tendsto_zero s).eventually_lt_const
      (by norm_num)
  filter_upwards [hthreshold, hsmall, hspan] with k hkWeight hkSmall hkSpan
  intro x hleft hright
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  have hweightPos :
      0 < etaCriticalMirrorContinuousWeightR s x :=
    etaCriticalMirrorContinuousWeightR_pos s hx
  have hsmallX :
      2 * |s.im| *
          ((‖criticalMirror s‖ + ‖s‖) *
            etaCriticalMirrorContinuousWeightR s x) *
          etaPairDerivativePhaseSpan s k ≤
        (s.im ^ 2 / 4) *
          etaCriticalMirrorContinuousWeightR s x := by
    have hm := mul_le_mul_of_nonneg_right hkSmall hweightPos.le
    convert hm using 1
    all_goals first | rfl | ring_nf
  exact
    etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_right_quarter_margin
      s k hleft hright hkSpan.le
      (hkWeight x hleft hright) hsmallX

/--
Left of the critical line, the explicit negative pointwise kernel margin holds
throughout every sufficiently late eta-pair interval.
-/
theorem eventually_neg_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_left_quarter_margin_on_pair
    {s : ℂ} (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        (s.im ^ 2 / 4) * etaPairRadialDecay s x ≤
          -etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x) := by
  have hthreshold :=
    eventually_etaCriticalMirrorContinuousWeightR_on_pair_le_half_of_re_lt_half
      hre
  have hsmall :=
    eventually_defectCoefficient_rotation_factor_le_quarter_vertical_margin
      s him
  have hspan :
      ∀ᶠ k : ℕ in atTop,
        etaPairDerivativePhaseSpan s k < 1 :=
    (etaPairDerivativePhaseSpan_tendsto_zero s).eventually_lt_const
      (by norm_num)
  filter_upwards [hthreshold, hsmall, hspan] with k hkWeight hkSmall hkSpan
  intro x hleft hright
  exact
    neg_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_left_quarter_margin
      s k hleft hright hkSpan.le
      (hkWeight x hleft hright) hkSmall

end DkMath.RH.CFBRCProjection
