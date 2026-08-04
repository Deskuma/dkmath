/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelQuantitativeMargin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairQuantitativeMargin"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter MeasureTheory
open scoped Topology

/-- Explicit positive pair margin on the growing-weight side. -/
noncomputable def etaCriticalMirrorRightPairMargin
    (s : ℂ) (k : ℕ) : ℝ :=
  ∫ x : ℝ in
      (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
    (s.im ^ 2 / 4) * etaPairRadialDecay s x *
      etaCriticalMirrorContinuousWeightR s x

/-- Explicit positive pair margin on the decaying-weight side. -/
noncomputable def etaCriticalMirrorLeftPairMargin
    (s : ℂ) (k : ℕ) : ℝ :=
  ∫ x : ℝ in
      (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
    (s.im ^ 2 / 4) * etaPairRadialDecay s x

private theorem etaPairFrameLeftEndpoint_le_rightEndpoint
    (k : ℕ) :
    etaPairFrameLeftEndpoint k ≤ etaPairFrameRightEndpoint k := by
  unfold etaPairFrameLeftEndpoint etaPairFrameRightEndpoint
  exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)

private theorem etaPairFrameLeftEndpoint_lt_rightEndpoint'
    (k : ℕ) :
    etaPairFrameLeftEndpoint k < etaPairFrameRightEndpoint k := by
  unfold etaPairFrameLeftEndpoint etaPairFrameRightEndpoint
  exact_mod_cast (by omega : 2 * k + 1 < 2 * k + 2)

private theorem etaPairRadialDecay_continuousOn_pair
    (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun x : ℝ => etaPairRadialDecay s x)
      (Set.uIcc (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k)) := by
  unfold etaPairRadialDecay
  apply continuousOn_id.rpow_const
  intro x hx
  left
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint k
  rw [Set.uIcc_of_le hle] at hx
  exact ((etaPairFrameLeftEndpoint_pos k).trans_le hx.1).ne'

private theorem etaCriticalMirrorContinuousWeightR_continuousOn_pair
    (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun x : ℝ => etaCriticalMirrorContinuousWeightR s x)
      (Set.uIcc (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k)) := by
  unfold etaCriticalMirrorContinuousWeightR
  apply continuousOn_id.rpow_const
  intro x hx
  left
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint k
  rw [Set.uIcc_of_le hle] at hx
  exact ((etaPairFrameLeftEndpoint_pos k).trans_le hx.1).ne'

private theorem etaCriticalMirrorRightPairMarginIntegrand_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        (s.im ^ 2 / 4) * etaPairRadialDecay s x *
          etaCriticalMirrorContinuousWeightR s x)
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  exact
    ((continuousOn_const.mul
      (etaPairRadialDecay_continuousOn_pair s k)).mul
        (etaCriticalMirrorContinuousWeightR_continuousOn_pair s k)).intervalIntegrable

private theorem etaCriticalMirrorLeftPairMarginIntegrand_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        (s.im ^ 2 / 4) * etaPairRadialDecay s x)
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  exact
    (continuousOn_const.mul
      (etaPairRadialDecay_continuousOn_pair s k)).intervalIntegrable

private theorem etaCriticalMirrorRotatedDefectKernelProjection_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x))
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  have hleft : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hle := etaPairFrameLeftEndpoint_le_rightEndpoint k
  have hcomplex :=
    (etaCriticalMirrorDefectPairIntegralKernel_intervalIntegrable
      s hleft hle).const_mul (etaPairBaseRotation s k)
  have him :
      IntervalIntegrable
        (fun x : ℝ =>
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x).im)
        volume
        (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k) :=
    ⟨hcomplex.1.im, hcomplex.2.im⟩
  simpa [etaCriticalMirrorSignedVerticalProjection] using
    him.const_mul s.im

private theorem criticalMirror_ne_zero_of_nontrivialRiemannZetaZero'
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    criticalMirror s ≠ 0 := by
  intro hm0
  have hpos := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  simp [hm0] at hpos

/-- The explicit right pair margin is strictly positive at a nonreal point. -/
theorem etaCriticalMirrorRightPairMargin_pos
    {s : ℂ} (him : s.im ≠ 0) (k : ℕ) :
    0 < etaCriticalMirrorRightPairMargin s k := by
  unfold etaCriticalMirrorRightPairMargin
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (etaCriticalMirrorRightPairMarginIntegrand_intervalIntegrable s k)
  · intro x hx
    have hx' : x ∈ Set.Icc
        (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k) :=
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hxpos : 0 < x :=
      (etaPairFrameLeftEndpoint_pos k).trans_le hx'.1
    exact mul_pos
      (mul_pos (by positivity) (etaPairRadialDecay_pos s hxpos))
      (etaCriticalMirrorContinuousWeightR_pos s hxpos)
  · exact etaPairFrameLeftEndpoint_lt_rightEndpoint' k

/-- The explicit left pair margin is strictly positive at a nonreal point. -/
theorem etaCriticalMirrorLeftPairMargin_pos
    {s : ℂ} (him : s.im ≠ 0) (k : ℕ) :
    0 < etaCriticalMirrorLeftPairMargin s k := by
  unfold etaCriticalMirrorLeftPairMargin
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (etaCriticalMirrorLeftPairMarginIntegrand_intervalIntegrable s k)
  · intro x hx
    have hxpos : 0 < x :=
      (etaPairFrameLeftEndpoint_pos k).trans_le hx.1.le
    exact mul_pos (by positivity) (etaPairRadialDecay_pos s hxpos)
  · exact etaPairFrameLeftEndpoint_lt_rightEndpoint' k

/-- Pointwise right-kernel control integrates to a pair-level projection margin. -/
theorem etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ)
    (hpoint :
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        (s.im ^ 2 / 4) * etaPairRadialDecay s x *
            etaCriticalMirrorContinuousWeightR s x ≤
          etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x)) :
    etaCriticalMirrorRightPairMargin s k ≤
      etaCriticalMirrorRotatedDefectPairProjection s k := by
  rw [etaCriticalMirrorRotatedDefectPairProjection,
    etaCriticalMirrorRotatedDefectPairTerm]
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_eq_intervalIntegral
    hs hm k]
  unfold etaCriticalMirrorRightPairMargin
  apply intervalIntegral.integral_mono_on
    (etaPairFrameLeftEndpoint_le_rightEndpoint k)
    (etaCriticalMirrorRightPairMarginIntegrand_intervalIntegrable s k)
    (etaCriticalMirrorRotatedDefectKernelProjection_intervalIntegrable s k)
  intro x hx
  exact hpoint x hx.1 hx.2

/-- Pointwise left-kernel control integrates to a pair-level negative margin. -/
theorem etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ)
    (hpoint :
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        (s.im ^ 2 / 4) * etaPairRadialDecay s x ≤
          -etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x)) :
    etaCriticalMirrorLeftPairMargin s k ≤
      -etaCriticalMirrorRotatedDefectPairProjection s k := by
  rw [etaCriticalMirrorRotatedDefectPairProjection,
    etaCriticalMirrorRotatedDefectPairTerm]
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_eq_intervalIntegral
    hs hm k]
  rw [← intervalIntegral.integral_neg]
  unfold etaCriticalMirrorLeftPairMargin
  apply intervalIntegral.integral_mono_on
    (etaPairFrameLeftEndpoint_le_rightEndpoint k)
    (etaCriticalMirrorLeftPairMarginIntegrand_intervalIntegrable s k)
    (etaCriticalMirrorRotatedDefectKernelProjection_intervalIntegrable s k).neg
  intro x hx
  exact hpoint x hx.1 hx.2

/-- Right of the critical line, the explicit pair margin eventually survives. -/
theorem eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorRightPairMargin s k ≤
        etaCriticalMirrorRotatedDefectPairProjection s k := by
  have hpoint :=
    eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_right_quarter_margin_on_pair
      him hre
  filter_upwards [hpoint] with k hk
  exact
    etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
      (nontrivialRiemannZetaZero_ne_zero hs)
      (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero' hs)
      k hk

/-- Left of the critical line, the explicit negative pair margin eventually survives. -/
theorem eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorLeftPairMargin s k ≤
        -etaCriticalMirrorRotatedDefectPairProjection s k := by
  have hpoint :=
    eventually_neg_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_ge_left_quarter_margin_on_pair
      him hre
  filter_upwards [hpoint] with k hk
  exact
    etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
      (nontrivialRiemannZetaZero_ne_zero hs)
      (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero' hs)
      k hk

end DkMath.RH.CFBRCProjection
