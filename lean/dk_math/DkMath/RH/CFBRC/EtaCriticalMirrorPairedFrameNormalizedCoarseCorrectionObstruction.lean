/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominationAudit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

namespace EtaPairPositiveDensityBlockSchedule

/--
For positive density and positive side parameter, the normalized density factor
is always strictly below one half.
-/
private theorem density_rpow_factor_lt_half
    {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    ρ * (1 + 2 * ρ) ^ (-1 - a) < (1 : ℝ) / 2 := by
  have hbase : 1 < (1 : ℝ) + 2 * ρ := by
    linarith
  have hbasePos : 0 < (1 : ℝ) + 2 * ρ :=
    lt_trans zero_lt_one hbase
  have hpowLeOne :
      ((1 : ℝ) + 2 * ρ) ^ (-a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase.le (by linarith)
  have hfrac :
      ρ / ((1 : ℝ) + 2 * ρ) < (1 : ℝ) / 2 := by
    rw [div_lt_iff₀ hbasePos]
    nlinarith
  have hfracNonneg :
      0 ≤ ρ / ((1 : ℝ) + 2 * ρ) :=
    div_nonneg hρ.le hbasePos.le
  calc
    ρ * ((1 : ℝ) + 2 * ρ) ^ (-1 - a) =
        (ρ / ((1 : ℝ) + 2 * ρ)) *
          ((1 : ℝ) + 2 * ρ) ^ (-a) := by
      rw [show -1 - a = (-1 : ℝ) + (-a) by ring]
      rw [Real.rpow_add hbasePos, Real.rpow_neg_one]
      ring
    _ ≤ (ρ / ((1 : ℝ) + 2 * ρ)) * 1 :=
      mul_le_mul_of_nonneg_left hpowLeOne hfracNonneg
    _ < (1 : ℝ) / 2 := by
      simpa using hfrac

/--
A complex norm majorant with side parameter `a ∈ (0, 1/2)` produces a
pair-left correction constant strictly larger than `8 * t^2`.
-/
private theorem eight_mul_sq_lt_coarse_endpoint_correction_constant
    {z : ℂ} {a t : ℝ}
    (hzre : z.re = a)
    (ha : 0 < a)
    (haHalf : a < (1 : ℝ) / 2)
    (ht : t ≠ 0) :
    8 * t ^ 2 <
      (2 : ℝ) ^ a *
        (|t| * ((4 * |t| / a) * (‖z‖ / a))) := by
  have hnorm : a ≤ ‖z‖ := by
    rw [← hzre]
    exact Complex.re_le_norm z
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos ha
  have hnormRatio : 2 < ‖z‖ / a ^ 2 := by
    rw [lt_div_iff₀ haSqPos]
    nlinarith
  have hrpowOne : 1 ≤ (2 : ℝ) ^ a :=
    Real.one_le_rpow (by norm_num) ha.le
  have hrpowPos : 0 < (2 : ℝ) ^ a :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcombined :
      2 < (2 : ℝ) ^ a * (‖z‖ / a ^ 2) := by
    calc
      2 = 2 * 1 := by ring
      _ ≤ 2 * ((2 : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_left hrpowOne (by norm_num)
      _ < (‖z‖ / a ^ 2) * ((2 : ℝ) ^ a) :=
        mul_lt_mul_of_pos_right hnormRatio hrpowPos
      _ = (2 : ℝ) ^ a * (‖z‖ / a ^ 2) := by ring
  have habsPos : 0 < |t| := abs_pos.mpr ht
  have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
  have hfourAbsSqPos : 0 < 4 * |t| ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos habsPos)
  have hscaled :=
    mul_lt_mul_of_pos_left hcombined hfourAbsSqPos
  have hrearrange :
      (2 : ℝ) ^ a *
          (|t| * ((4 * |t| / a) * (‖z‖ / a))) =
        (4 * |t| ^ 2) *
          ((2 : ℝ) ^ a * (‖z‖ / a ^ 2)) := by
    field_simp [ha.ne']
  calc
    8 * t ^ 2 = (4 * |t| ^ 2) * 2 := by
      rw [habsSq]
      ring
    _ < (4 * |t| ^ 2) *
        ((2 : ℝ) ^ a * (‖z‖ / a ^ 2)) := hscaled
    _ = (2 : ℝ) ^ a *
        (|t| * ((4 * |t| / a) * (‖z‖ / a))) :=
      hrearrange.symm

/-- Every positive-density right block constant is below `im(s)^2 / 8`. -/
theorem rightNormalizedBlockMarginConstant_lt_im_sq_div_eight
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    S.rightNormalizedBlockMarginConstant s < s.im ^ 2 / 8 := by
  have ha : 0 < (1 : ℝ) - s.re := by
    linarith [nontrivialRiemannZetaZero_re_lt_one hs]
  have hfactor := density_rpow_factor_lt_half S.density_pos ha
  have hfactor' :
      S.density *
          (1 + 2 * S.density) ^ (s.re - 2) <
        (1 : ℝ) / 2 := by
    convert hfactor using 1
    ring_nf
  have hcoeff : 0 < s.im ^ 2 / 4 :=
    div_pos (sq_pos_of_ne_zero him) (by norm_num)
  unfold rightNormalizedBlockMarginConstant
  calc
    (s.im ^ 2 / 4) *
        (S.density *
          (1 + 2 * S.density) ^ (s.re - 2)) <
      (s.im ^ 2 / 4) * ((1 : ℝ) / 2) :=
        mul_lt_mul_of_pos_left hfactor' hcoeff
    _ = s.im ^ 2 / 8 := by ring

/-- Every positive-density left block constant is below `im(s)^2 / 8`. -/
theorem leftNormalizedBlockMarginConstant_lt_im_sq_div_eight
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    S.leftNormalizedBlockMarginConstant s < s.im ^ 2 / 8 := by
  have ha : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hfactor := density_rpow_factor_lt_half S.density_pos ha
  have hfactor' :
      S.density *
          (1 + 2 * S.density) ^ (-s.re - 1) <
        (1 : ℝ) / 2 := by
    convert hfactor using 1
    ring_nf
  have hcoeff : 0 < s.im ^ 2 / 4 :=
    div_pos (sq_pos_of_ne_zero him) (by norm_num)
  unfold leftNormalizedBlockMarginConstant
  calc
    (s.im ^ 2 / 4) *
        (S.density *
          (1 + 2 * S.density) ^ (-s.re - 1)) <
      (s.im ^ 2 / 4) * ((1 : ℝ) / 2) :=
        mul_lt_mul_of_pos_left hfactor' hcoeff
    _ = s.im ^ 2 / 8 := by ring

/-- On the right, the coarse pair-left correction constant exceeds `8 * im(s)^2`. -/
theorem eight_mul_im_sq_lt_rightLeftEndpointNormalizedCorrectionConstant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    8 * s.im ^ 2 <
      etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s := by
  unfold etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant
  unfold etaCriticalMirrorCorrectionMirrorProjectionConstant
  apply eight_mul_sq_lt_coarse_endpoint_correction_constant
      (z := criticalMirror s) (a := (criticalMirror s).re) (t := s.im)
  · rfl
  · exact criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  · rw [criticalMirror_re]
    linarith
  · exact him

/-- On the left, the coarse pair-left correction constant exceeds `8 * im(s)^2`. -/
theorem eight_mul_im_sq_lt_leftLeftEndpointNormalizedCorrectionConstant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    8 * s.im ^ 2 <
      etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s := by
  unfold etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant
  unfold etaCriticalMirrorCorrectionOriginalProjectionConstant
  apply eight_mul_sq_lt_coarse_endpoint_correction_constant
      (z := s) (a := s.re) (t := s.im)
  · rfl
  · exact nontrivialRiemannZetaZero_re_pos hs
  · exact hre
  · exact him

/--
The right normalized block constant is strictly smaller than the coarse
pair-left correction constant for every positive-density schedule.
-/
theorem rightNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    S.rightNormalizedBlockMarginConstant s <
      etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s := by
  have hblock :=
    S.rightNormalizedBlockMarginConstant_lt_im_sq_div_eight hs him
  have hcorr :=
    eight_mul_im_sq_lt_rightLeftEndpointNormalizedCorrectionConstant
      hs him hre
  have himSqPos : 0 < s.im ^ 2 := sq_pos_of_ne_zero him
  nlinarith

/--
The left normalized block constant is strictly smaller than the coarse
pair-left correction constant for every positive-density schedule.
-/
theorem leftNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    S.leftNormalizedBlockMarginConstant s <
      etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s := by
  have hblock :=
    S.leftNormalizedBlockMarginConstant_lt_im_sq_div_eight hs him
  have hcorr :=
    eight_mul_im_sq_lt_leftLeftEndpointNormalizedCorrectionConstant
      hs him hre
  have himSqPos : 0 < s.im ^ 2 := sq_pos_of_ne_zero him
  nlinarith

/-- The current coarse right constant domination gate is impossible. -/
theorem not_rightNormalizedAbelCorrectionConstantDominates
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ S.RightNormalizedAbelCorrectionConstantDominates s := by
  intro hdom
  unfold RightNormalizedAbelCorrectionConstantDominates at hdom
  exact not_lt_of_ge (S.rightNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    hs him hre).le hdom

/-- The current coarse left constant domination gate is impossible. -/
theorem not_leftNormalizedAbelCorrectionConstantDominates
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ S.LeftNormalizedAbelCorrectionConstantDominates s := by
  intro hdom
  unfold LeftNormalizedAbelCorrectionConstantDominates at hdom
  exact not_lt_of_ge (S.leftNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    hs him hre).le hdom

/-- The right block-minus-coarse-correction constant gap is strictly negative. -/
theorem rightNormalizedAbelCorrectionDominationGap_neg
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    S.rightNormalizedAbelCorrectionDominationGap s < 0 := by
  unfold rightNormalizedAbelCorrectionDominationGap
  linarith [S.rightNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    hs him hre]

/-- The left block-minus-coarse-correction constant gap is strictly negative. -/
theorem leftNormalizedAbelCorrectionDominationGap_neg
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    S.leftNormalizedAbelCorrectionDominationGap s < 0 := by
  unfold leftNormalizedAbelCorrectionDominationGap
  linarith [S.leftNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    hs him hre]

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
