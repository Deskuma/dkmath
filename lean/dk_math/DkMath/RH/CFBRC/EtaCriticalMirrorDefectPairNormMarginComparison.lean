/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairQuantitativeMargin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairNormMarginComparison"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter MeasureTheory
open scoped Topology

/-- Common coefficient controlling the norm of the continuous mirror defect. -/
noncomputable def etaCriticalMirrorDefectPairNormCoefficient
    (s : ℂ) : ℝ :=
  ‖criticalMirror s‖ + ‖s‖

/-- The common norm coefficient is nonnegative. -/
theorem etaCriticalMirrorDefectPairNormCoefficient_nonneg
    (s : ℂ) :
    0 ≤ etaCriticalMirrorDefectPairNormCoefficient s := by
  unfold etaCriticalMirrorDefectPairNormCoefficient
  positivity

private theorem etaPairFrameLeftEndpoint_le_rightEndpoint_normMargin
    (k : ℕ) :
    etaPairFrameLeftEndpoint k ≤ etaPairFrameRightEndpoint k := by
  unfold etaPairFrameLeftEndpoint etaPairFrameRightEndpoint
  exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)

private theorem etaPairRadialDecay_continuousOn_pair_normMargin
    (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun x : ℝ => etaPairRadialDecay s x)
      (Set.uIcc (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k)) := by
  unfold etaPairRadialDecay
  apply continuousOn_id.rpow_const
  intro x hx
  left
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_normMargin k
  rw [Set.uIcc_of_le hle] at hx
  exact ((etaPairFrameLeftEndpoint_pos k).trans_le hx.1).ne'

private theorem etaCriticalMirrorContinuousWeightR_continuousOn_pair_normMargin
    (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun x : ℝ => etaCriticalMirrorContinuousWeightR s x)
      (Set.uIcc (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k)) := by
  unfold etaCriticalMirrorContinuousWeightR
  apply continuousOn_id.rpow_const
  intro x hx
  left
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_normMargin k
  rw [Set.uIcc_of_le hle] at hx
  exact ((etaPairFrameLeftEndpoint_pos k).trans_le hx.1).ne'

private theorem etaCriticalMirrorRightScaledNormDensity_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        etaCriticalMirrorDefectPairNormCoefficient s *
          ((s.im ^ 2 / 4) * etaPairRadialDecay s x *
            etaCriticalMirrorContinuousWeightR s x))
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  exact
    (continuousOn_const.mul
      ((continuousOn_const.mul
        (etaPairRadialDecay_continuousOn_pair_normMargin s k)).mul
          (etaCriticalMirrorContinuousWeightR_continuousOn_pair_normMargin s k))).intervalIntegrable

private theorem etaCriticalMirrorLeftScaledNormDensity_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        etaCriticalMirrorDefectPairNormCoefficient s *
          ((s.im ^ 2 / 4) * etaPairRadialDecay s x))
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  exact
    (continuousOn_const.mul
      (continuousOn_const.mul
        (etaPairRadialDecay_continuousOn_pair_normMargin s k))).intervalIntegrable

private theorem norm_scaled_etaPairBaseRotation_mul_defectPairIntegralKernel_le_right_density
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hx : 0 < x)
    (hweight : 1 ≤ etaCriticalMirrorContinuousWeightR s x) :
    ‖((s.im ^ 2 / 4 : ℝ) : ℂ) *
        (etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x)‖ ≤
      etaCriticalMirrorDefectPairNormCoefficient s *
        ((s.im ^ 2 / 4) * etaPairRadialDecay s x *
          etaCriticalMirrorContinuousWeightR s x) := by
  have ha : 0 ≤ s.im ^ 2 / 4 := by positivity
  have hr : 0 ≤ etaPairRadialDecay s x :=
    (etaPairRadialDecay_pos s hx).le
  have hcoeff :
      ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorContinuousWeightR s x := by
    simpa [etaCriticalMirrorDefectPairNormCoefficient] using
      norm_etaCriticalMirrorDefectCoefficient_le_right_linear
        s hx hweight
  rw [etaPairBaseRotation_mul_defectPairIntegralKernel_factor s k hx]
  calc
    ‖((s.im ^ 2 / 4 : ℝ) : ℂ) *
        (((etaPairRadialDecay s x : ℝ) : ℂ) *
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x))‖ =
        (s.im ^ 2 / 4) *
          (etaPairRadialDecay s x *
            ‖etaCriticalMirrorDefectCoefficient s x‖) := by
      simp [norm_etaPairResidualRotation, abs_of_nonneg hr]
    _ ≤
        (s.im ^ 2 / 4) *
          (etaPairRadialDecay s x *
            (etaCriticalMirrorDefectPairNormCoefficient s *
              etaCriticalMirrorContinuousWeightR s x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcoeff hr) ha
    _ =
        etaCriticalMirrorDefectPairNormCoefficient s *
          ((s.im ^ 2 / 4) * etaPairRadialDecay s x *
            etaCriticalMirrorContinuousWeightR s x) := by
      ring

private theorem norm_scaled_etaPairBaseRotation_mul_defectPairIntegralKernel_le_left_density
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hx : 0 < x)
    (hweight : etaCriticalMirrorContinuousWeightR s x ≤ 1) :
    ‖((s.im ^ 2 / 4 : ℝ) : ℂ) *
        (etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x)‖ ≤
      etaCriticalMirrorDefectPairNormCoefficient s *
        ((s.im ^ 2 / 4) * etaPairRadialDecay s x) := by
  have ha : 0 ≤ s.im ^ 2 / 4 := by positivity
  have hr : 0 ≤ etaPairRadialDecay s x :=
    (etaPairRadialDecay_pos s hx).le
  have hcoeff :
      ‖etaCriticalMirrorDefectCoefficient s x‖ ≤
        etaCriticalMirrorDefectPairNormCoefficient s := by
    simpa [etaCriticalMirrorDefectPairNormCoefficient] using
      norm_etaCriticalMirrorDefectCoefficient_le_left_bounded
        s hx hweight
  rw [etaPairBaseRotation_mul_defectPairIntegralKernel_factor s k hx]
  calc
    ‖((s.im ^ 2 / 4 : ℝ) : ℂ) *
        (((etaPairRadialDecay s x : ℝ) : ℂ) *
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x))‖ =
        (s.im ^ 2 / 4) *
          (etaPairRadialDecay s x *
            ‖etaCriticalMirrorDefectCoefficient s x‖) := by
      simp [norm_etaPairResidualRotation, abs_of_nonneg hr]
    _ ≤
        (s.im ^ 2 / 4) *
          (etaPairRadialDecay s x *
            etaCriticalMirrorDefectPairNormCoefficient s) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcoeff hr) ha
    _ =
        etaCriticalMirrorDefectPairNormCoefficient s *
          ((s.im ^ 2 / 4) * etaPairRadialDecay s x) := by
      ring

/--
On a pair where the transport weight is at least one, the defect-pair norm,
scaled by the vertical margin coefficient, is controlled by the explicit
right pair margin.
-/
theorem scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ)
    (hweight :
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        1 ≤ etaCriticalMirrorContinuousWeightR s x) :
    (s.im ^ 2 / 4) * ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      etaCriticalMirrorDefectPairNormCoefficient s *
        etaCriticalMirrorRightPairMargin s k := by
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_normMargin k
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x : ℝ =>
        ((s.im ^ 2 / 4 : ℝ) : ℂ) *
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x))
      hle
      (Filter.Eventually.of_forall fun x hxIoc => by
        have hleft : etaPairFrameLeftEndpoint k ≤ x := hxIoc.1.le
        have hright : x ≤ etaPairFrameRightEndpoint k := hxIoc.2
        have hx : 0 < x :=
          (etaPairFrameLeftEndpoint_pos k).trans_le hleft
        exact
          norm_scaled_etaPairBaseRotation_mul_defectPairIntegralKernel_le_right_density
            s k hx (hweight x hleft hright))
      (etaCriticalMirrorRightScaledNormDensity_intervalIntegrable s k)
  have hleftEq :
      ‖∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        ((s.im ^ 2 / 4 : ℝ) : ℂ) *
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x)‖ =
        (s.im ^ 2 / 4) *
          ‖etaCriticalMirrorDefectPairTerm s k‖ := by
    rw [intervalIntegral.integral_const_mul]
    rw [← etaPairBaseRotation_mul_defectPairTerm_eq_intervalIntegral
      hs hm k]
    simp [norm_etaPairBaseRotation]
  have hrightEq :
      (∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        etaCriticalMirrorDefectPairNormCoefficient s *
          ((s.im ^ 2 / 4) * etaPairRadialDecay s x *
            etaCriticalMirrorContinuousWeightR s x)) =
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorRightPairMargin s k := by
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [hleftEq, hrightEq] at hnorm
  exact hnorm

/--
On a pair where the transport weight is at most one, the same scaled defect
norm is controlled by the explicit left pair margin.
-/
theorem scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ)
    (hweight :
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorContinuousWeightR s x ≤ 1) :
    (s.im ^ 2 / 4) * ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      etaCriticalMirrorDefectPairNormCoefficient s *
        etaCriticalMirrorLeftPairMargin s k := by
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint_normMargin k
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x : ℝ =>
        ((s.im ^ 2 / 4 : ℝ) : ℂ) *
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x))
      hle
      (Filter.Eventually.of_forall fun x hxIoc => by
        have hleft : etaPairFrameLeftEndpoint k ≤ x := hxIoc.1.le
        have hright : x ≤ etaPairFrameRightEndpoint k := hxIoc.2
        have hx : 0 < x :=
          (etaPairFrameLeftEndpoint_pos k).trans_le hleft
        exact
          norm_scaled_etaPairBaseRotation_mul_defectPairIntegralKernel_le_left_density
            s k hx (hweight x hleft hright))
      (etaCriticalMirrorLeftScaledNormDensity_intervalIntegrable s k)
  have hleftEq :
      ‖∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        ((s.im ^ 2 / 4 : ℝ) : ℂ) *
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x)‖ =
        (s.im ^ 2 / 4) *
          ‖etaCriticalMirrorDefectPairTerm s k‖ := by
    rw [intervalIntegral.integral_const_mul]
    rw [← etaPairBaseRotation_mul_defectPairTerm_eq_intervalIntegral
      hs hm k]
    simp [norm_etaPairBaseRotation]
  have hrightEq :
      (∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        etaCriticalMirrorDefectPairNormCoefficient s *
          ((s.im ^ 2 / 4) * etaPairRadialDecay s x)) =
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorLeftPairMargin s k := by
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [hleftEq, hrightEq] at hnorm
  exact hnorm

private theorem criticalMirror_ne_zero_of_nontrivialRiemannZetaZero_normMargin
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    criticalMirror s ≠ 0 := by
  intro hm0
  have hpos := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  simp [hm0] at hpos

/-- Right of the critical line, the scaled norm-to-margin comparison is eventual. -/
theorem eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      (s.im ^ 2 / 4) * ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorRightPairMargin s k := by
  have hthreshold :=
    eventually_two_le_etaCriticalMirrorContinuousWeightR_on_pair_of_half_lt_re
      hre
  filter_upwards [hthreshold] with k hk
  apply
    scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
      (nontrivialRiemannZetaZero_ne_zero hs)
      (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero_normMargin hs)
      k
  intro x hleft hright
  exact (show (1 : ℝ) ≤ 2 by norm_num).trans
    (hk x hleft hright)

/-- Left of the critical line, the scaled norm-to-margin comparison is eventual. -/
theorem eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      (s.im ^ 2 / 4) * ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorLeftPairMargin s k := by
  have hthreshold :=
    eventually_etaCriticalMirrorContinuousWeightR_on_pair_le_half_of_re_lt_half
      hre
  filter_upwards [hthreshold] with k hk
  apply
    scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
      (nontrivialRiemannZetaZero_ne_zero hs)
      (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero_normMargin hs)
      k
  intro x hleft hright
  exact (hk x hleft hright).trans (by norm_num)

end DkMath.RH.CFBRCProjection
