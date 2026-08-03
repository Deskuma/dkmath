/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightPressure
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientProjection"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/--
Signed projection onto the vertical direction determined by `s`.

Multiplying the imaginary coordinate by `s.im` removes the distinction between
the upper and lower half-planes.  Positive and negative values can therefore
encode only the right/left pressure relative to the critical line.
-/
def etaCriticalMirrorSignedVerticalProjection
    (s z : ℂ) : ℝ :=
  s.im * z.im

/--
The signed vertical projection of the continuous defect coefficient is exactly
`s.im²` times the transport-weight displacement from one.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) =
      s.im ^ 2 *
        (etaCriticalMirrorContinuousWeightR s x - 1) := by
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [etaCriticalMirrorDefectCoefficient_im s hx]
  ring

/--
At a nonreal point right of the critical line, the signed vertical projection
of the defect coefficient is strictly positive for every `x > 1`.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_pos_of_half_lt_re
    {s : ℂ} (him : s.im ≠ 0)
    (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    0 <
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq
    s (lt_trans zero_lt_one hx)]
  exact mul_pos
    (sq_pos_of_ne_zero him)
    (sub_pos.mpr
      (one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hre hx))

/--
At a nonreal point left of the critical line, the signed vertical projection
of the defect coefficient is strictly negative for every `x > 1`.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_neg_of_re_lt_half
    {s : ℂ} (him : s.im ≠ 0)
    (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) < 0 := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq
    s (lt_trans zero_lt_one hx)]
  exact mul_neg_of_pos_of_neg
    (sq_pos_of_ne_zero him)
    (sub_neg.mpr
      (etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hre hx))

/-- On the critical line, the signed vertical projection vanishes. -/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq_zero_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) = 0 := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq s hx]
  rw [etaCriticalMirrorContinuousWeightR_eq_one_of_re_eq_half hre x]
  ring

/--
Complete left/center/right sign classification of the signed vertical defect
coefficient projection at every informative positive-real point `x > 1`.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_sign_trichotomy
    (s : ℂ) (him : s.im ≠ 0)
    {x : ℝ} (hx : 1 < x) :
    (s.re < (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) < 0) ∨
    (s.re = (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) = 0) ∨
    ((1 : ℝ) / 2 < s.re ∧
      0 < etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)) := by
  rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
  · exact Or.inl ⟨hleft,
      etaCriticalMirrorSignedVerticalProjection_defectCoefficient_neg_of_re_lt_half
        him hleft hx⟩
  · exact Or.inr <| Or.inl ⟨hline,
      etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq_zero_of_re_eq_half
        hline (lt_trans zero_lt_one hx)⟩
  · exact Or.inr <| Or.inr ⟨hright,
      etaCriticalMirrorSignedVerticalProjection_defectCoefficient_pos_of_half_lt_re
        him hright hx⟩

/--
Multiplication by a nearby rotation changes the signed vertical projection by
at most the rotation chord times `|s.im|` and the coefficient norm.
-/
theorem abs_etaCriticalMirrorSignedVerticalProjection_mul_sub_le
    (s c r : ℂ) :
    |etaCriticalMirrorSignedVerticalProjection s (c * r) -
        etaCriticalMirrorSignedVerticalProjection s c| ≤
      |s.im| * ‖c‖ * ‖r - 1‖ := by
  unfold etaCriticalMirrorSignedVerticalProjection
  have hdiff :
      s.im * (c * r).im - s.im * c.im =
        s.im * (c * r - c).im := by
    simp
    ring
  rw [hdiff, abs_mul]
  calc
    |s.im| * |(c * r - c).im| ≤
        |s.im| * ‖c * r - c‖ :=
      mul_le_mul_of_nonneg_left
        (Complex.abs_im_le_norm (c * r - c))
        (abs_nonneg s.im)
    _ = |s.im| * (‖c‖ * ‖r - 1‖) := by
      rw [show c * r - c = c * (r - 1) by ring, norm_mul]
    _ = |s.im| * ‖c‖ * ‖r - 1‖ := by ring

/--
For residual phase at most one radian, the residual unit-circle chord is at
most twice the absolute phase.
-/
theorem norm_etaPairResidualRotation_sub_one_le_two_mul_abs_phase
    (s : ℂ) (k : ℕ) (x : ℝ)
    (hphase : |etaPairResidualPhase s k x| ≤ 1) :
    ‖etaPairResidualRotation s k x - 1‖ ≤
      2 * |etaPairResidualPhase s k x| := by
  let z : ℂ :=
    Complex.I *
      ((-etaPairResidualPhase s k x : ℝ) : ℂ)
  have hz : ‖z‖ = |etaPairResidualPhase s k x| := by
    simp [z]
  rw [etaPairResidualRotation]
  change ‖Complex.exp z - 1‖ ≤
    2 * |etaPairResidualPhase s k x|
  calc
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ :=
      Complex.norm_exp_sub_one_le (by simpa [hz] using hphase)
    _ = 2 * |etaPairResidualPhase s k x| := by rw [hz]

/--
The signed vertical projection error for the actual defect coefficient under
its pair-local residual rotation is bounded linearly by the residual phase.
-/
theorem abs_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_sub_le
    (s : ℂ) (k : ℕ) (x : ℝ)
    (hphase : |etaPairResidualPhase s k x| ≤ 1) :
    |etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) -
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x)| ≤
      2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
        |etaPairResidualPhase s k x| := by
  calc
    |etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) -
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x)| ≤
        |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
          ‖etaPairResidualRotation s k x - 1‖ :=
      abs_etaCriticalMirrorSignedVerticalProjection_mul_sub_le
        s (etaCriticalMirrorDefectCoefficient s x)
        (etaPairResidualRotation s k x)
    _ ≤
        |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
          (2 * |etaPairResidualPhase s k x|) :=
      mul_le_mul_of_nonneg_left
        (norm_etaPairResidualRotation_sub_one_le_two_mul_abs_phase
          s k x hphase)
        (mul_nonneg (abs_nonneg s.im)
          (norm_nonneg (etaCriticalMirrorDefectCoefficient s x)))
    _ =
        2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
          |etaPairResidualPhase s k x| := by ring

/--
Inside one eta-pair interval, the preceding rotation error is controlled by
the already established pair phase span.
-/
theorem abs_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_sub_le_phaseSpan
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspan : etaPairDerivativePhaseSpan s k ≤ 1) :
    |etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) -
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x)| ≤
      2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
        etaPairDerivativePhaseSpan s k := by
  have hphase :
      |etaPairResidualPhase s k x| ≤
        etaPairDerivativePhaseSpan s k :=
    abs_etaPairResidualPhase_le_phaseSpan s k hleft hright
  have hphaseOne : |etaPairResidualPhase s k x| ≤ 1 :=
    hphase.trans hspan
  calc
    |etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) -
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x)| ≤
        2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
          |etaPairResidualPhase s k x| :=
      abs_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_sub_le
        s k x hphaseOne
    _ ≤
        2 * |s.im| * ‖etaCriticalMirrorDefectCoefficient s x‖ *
          etaPairDerivativePhaseSpan s k :=
      mul_le_mul_of_nonneg_left hphase (by positivity)

/-- A positive coefficient projection survives whenever the rotation error is smaller. -/
theorem etaCriticalMirrorSignedVerticalProjection_mul_pos_of_rotation_error_lt
    {s c r : ℂ}
    (hbase : 0 < etaCriticalMirrorSignedVerticalProjection s c)
    (herr :
      |etaCriticalMirrorSignedVerticalProjection s (c * r) -
        etaCriticalMirrorSignedVerticalProjection s c| <
        etaCriticalMirrorSignedVerticalProjection s c) :
    0 < etaCriticalMirrorSignedVerticalProjection s (c * r) := by
  have hlower := neg_lt_of_abs_lt herr
  linarith

/-- A negative coefficient projection survives whenever the rotation error is smaller. -/
theorem etaCriticalMirrorSignedVerticalProjection_mul_neg_of_rotation_error_lt
    {s c r : ℂ}
    (hbase : etaCriticalMirrorSignedVerticalProjection s c < 0)
    (herr :
      |etaCriticalMirrorSignedVerticalProjection s (c * r) -
        etaCriticalMirrorSignedVerticalProjection s c| <
        -etaCriticalMirrorSignedVerticalProjection s c) :
    etaCriticalMirrorSignedVerticalProjection s (c * r) < 0 := by
  have hupper := lt_of_abs_lt herr
  linarith

end DkMath.RH.CFBRCProjection
