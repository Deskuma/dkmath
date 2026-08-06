/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientProjection
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientMargin"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-- The continuous transport weight has norm equal to its positive real form. -/
theorem norm_etaCriticalMirrorContinuousWeight
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖etaCriticalMirrorContinuousWeight s x‖ =
      etaCriticalMirrorContinuousWeightR s x := by
  rw [etaCriticalMirrorContinuousWeight_eq_ofReal s hx]
  simp [abs_of_pos (etaCriticalMirrorContinuousWeightR_pos s hx)]

/-- Triangle bound for the continuous defect coefficient. -/
theorem norm_etaCriticalMirrorDefectCoefficient_le_transport
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
      ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x +
        ‖s‖ := by
  unfold etaCriticalMirrorDefectCoefficient
  calc
    ‖criticalMirror s * etaCriticalMirrorContinuousWeight s x - s‖ ≤
        ‖criticalMirror s * etaCriticalMirrorContinuousWeight s x‖ +
          ‖s‖ := norm_sub_le _ _
    _ =
        ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x +
          ‖s‖ := by
      rw [norm_mul, norm_etaCriticalMirrorContinuousWeight s hx]

/-- On the growing-weight side, the coefficient norm is at most linear in the weight. -/
theorem norm_etaCriticalMirrorDefectCoefficient_le_right_linear
    (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : 1 ≤ etaCriticalMirrorContinuousWeightR s x) :
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
      (‖criticalMirror s‖ + ‖s‖) *
        etaCriticalMirrorContinuousWeightR s x := by
  have hs :
      ‖s‖ ≤ ‖s‖ * etaCriticalMirrorContinuousWeightR s x := by
    calc
      ‖s‖ = ‖s‖ * 1 := by ring
      _ ≤ ‖s‖ * etaCriticalMirrorContinuousWeightR s x :=
        mul_le_mul_of_nonneg_left hweight (norm_nonneg s)
  calc
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
        ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x +
          ‖s‖ :=
      norm_etaCriticalMirrorDefectCoefficient_le_transport s hx
    _ ≤
        ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x +
          ‖s‖ * etaCriticalMirrorContinuousWeightR s x :=
      add_le_add_right hs _
    _ =
        (‖criticalMirror s‖ + ‖s‖) *
          etaCriticalMirrorContinuousWeightR s x := by ring

/-- On the decaying-weight side, the coefficient norm is uniformly bounded. -/
theorem norm_etaCriticalMirrorDefectCoefficient_le_left_bounded
    (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ 1) :
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
      ‖criticalMirror s‖ + ‖s‖ := by
  have hm :
      ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x ≤
        ‖criticalMirror s‖ := by
    calc
      ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x ≤
          ‖criticalMirror s‖ * 1 :=
        mul_le_mul_of_nonneg_left hweight (norm_nonneg (criticalMirror s))
      _ = ‖criticalMirror s‖ := by ring
  calc
    ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
        ‖criticalMirror s‖ * etaCriticalMirrorContinuousWeightR s x +
          ‖s‖ :=
      norm_etaCriticalMirrorDefectCoefficient_le_transport s hx
    _ ≤ ‖criticalMirror s‖ + ‖s‖ := add_le_add_left hm _

/-- If the growing transport weight is at least two, half its quadratic pressure survives. -/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_right_margin
    (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : 2 ≤ etaCriticalMirrorContinuousWeightR s x) :
    (s.im ^ 2 / 2) * etaCriticalMirrorContinuousWeightR s x ≤
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq s hx]
  nlinarith [sq_nonneg s.im]

/-- If the decaying transport weight is at most one half, a fixed negative pressure survives. -/
theorem neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_left_margin
    (s : ℂ) {x : ℝ} (hx : 0 < x)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2) :
    s.im ^ 2 / 2 ≤
      -etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq s hx]
  nlinarith [sq_nonneg s.im]

/--
A right-side coefficient keeps positive signed projection after pair-local
residual rotation whenever the explicit norm-phase majorant fits below the
surviving right margin.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_pos_of_right_margin
    (s : ℂ) (k : ℕ) {x : ℝ}
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
  have hmargin :=
    etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_right_margin
      s hx hweight
  apply etaCriticalMirrorSignedVerticalProjection_mul_pos_of_rotation_error_lt
  exact herror.trans_lt (hsmall.trans_le hmargin)

/--
A left-side coefficient keeps negative signed projection after pair-local
residual rotation whenever the explicit norm-phase majorant fits below the
surviving left margin.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_neg_of_left_margin
    (s : ℂ) (k : ℕ) {x : ℝ}
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
        etaPairResidualRotation s k x) < 0 := by
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
  have hmargin :=
    neg_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_ge_left_margin
      s hx hweight
  apply etaCriticalMirrorSignedVerticalProjection_mul_neg_of_rotation_error_lt
  exact herror.trans_lt (hsmall.trans_le hmargin)

end DkMath.RH.CFBRCProjection
