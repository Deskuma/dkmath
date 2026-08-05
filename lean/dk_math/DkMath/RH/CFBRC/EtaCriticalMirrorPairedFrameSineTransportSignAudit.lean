/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportSignAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- The logarithmic increment between two adjacent pair-left endpoints is positive. -/
theorem etaPairFrameLogStep_pos (k : ℕ) :
    0 <
      Real.log (etaPairFrameLeftEndpoint (k + 1)) -
        Real.log (etaPairFrameLeftEndpoint k) := by
  have ha : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hb : 0 < etaPairFrameLeftEndpoint (k + 1) :=
    etaPairFrameLeftEndpoint_pos (k + 1)
  have hab :
      etaPairFrameLeftEndpoint k <
        etaPairFrameLeftEndpoint (k + 1) := by
    unfold etaPairFrameLeftEndpoint
    exact_mod_cast (by omega : 2 * k + 1 < 2 * (k + 1) + 1)
  have hratio :
      1 <
        etaPairFrameLeftEndpoint (k + 1) /
          etaPairFrameLeftEndpoint k := by
    rw [lt_div_iff₀ ha]
    simpa using hab
  rw [← Real.log_div hb.ne' ha.ne']
  exact Real.log_pos hratio

/-- A positive imaginary part gives a positive adjacent pair-frame phase. -/
theorem etaPairFrameStepPhase_pos_of_im_pos
    {s : ℂ} (him : 0 < s.im) (k : ℕ) :
    0 < etaPairFrameStepPhase s k := by
  unfold etaPairFrameStepPhase
  exact mul_pos him (etaPairFrameLogStep_pos k)

/-- A negative imaginary part gives a negative adjacent pair-frame phase. -/
theorem etaPairFrameStepPhase_neg_of_im_neg
    {s : ℂ} (him : s.im < 0) (k : ℕ) :
    etaPairFrameStepPhase s k < 0 := by
  unfold etaPairFrameStepPhase
  exact mul_neg_of_neg_of_pos him (etaPairFrameLogStep_pos k)

/-- At a nonreal point every adjacent pair-frame phase is nonzero. -/
theorem etaPairFrameStepPhase_ne_zero_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) (k : ℕ) :
    etaPairFrameStepPhase s k ≠ 0 := by
  unfold etaPairFrameStepPhase
  exact mul_ne_zero him (etaPairFrameLogStep_pos k).ne'

/-- Signed first-order coefficient in the sine-transport correction term. -/
noncomputable def etaCriticalMirrorPairedFrameSineTransportCoefficient
    (s : ℂ) (k : ℕ) : ℝ :=
  s.im * Real.sin (etaPairFrameStepPhase s k)

/--
Eventually the signed sine-transport coefficient is strictly positive at every
nonreal point.  The frame phase has the sign of `s.im`, and eventually lies in
`(-π/2, π/2)`, where sine has the same sign as its argument.
-/
theorem eventually_etaCriticalMirrorPairedFrameSineTransportCoefficient_pos
    {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      0 < etaCriticalMirrorPairedFrameSineTransportCoefficient s k := by
  filter_upwards [eventually_etaPairFrameStepSpan_lt_pi_div_two s] with k hspan
  have habs :
      |etaPairFrameStepPhase s k| < Real.pi / 2 := by
    rw [abs_etaPairFrameStepPhase]
    exact hspan
  rcases lt_or_gt_of_ne him with himNeg | himPos
  · have hphaseNeg : etaPairFrameStepPhase s k < 0 :=
      etaPairFrameStepPhase_neg_of_im_neg himNeg k
    have hnegPi : -Real.pi < etaPairFrameStepPhase s k := by
      have hleft := (abs_lt.mp habs).1
      linarith [Real.pi_pos]
    have hsinNeg : Real.sin (etaPairFrameStepPhase s k) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hphaseNeg hnegPi
    unfold etaCriticalMirrorPairedFrameSineTransportCoefficient
    exact mul_pos_of_neg_of_neg himNeg hsinNeg
  · have hphasePos : 0 < etaPairFrameStepPhase s k :=
      etaPairFrameStepPhase_pos_of_im_pos himPos k
    have hphasePi : etaPairFrameStepPhase s k < Real.pi := by
      have hright := (abs_lt.mp habs).2
      linarith [Real.pi_pos]
    have hsinPos : 0 < Real.sin (etaPairFrameStepPhase s k) :=
      Real.sin_pos_of_pos_of_lt_pi hphasePos hphasePi
    unfold etaCriticalMirrorPairedFrameSineTransportCoefficient
    exact mul_pos himPos hsinPos

/-- The defect tail transported into the current pair-left frame. -/
noncomputable def etaCriticalMirrorPairFrameRotatedDefectTail
    (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k *
    etaCriticalMirrorDefectPairTail (k + 1) s

/--
At a nonreal nontrivial zero, the transported defect partial is exactly the
negative rotated remaining defect tail.
-/
theorem etaCriticalMirrorPairFrameTransportedDefectPartial_eq_neg_rotatedDefectTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorPairFrameTransportedDefectPartial s k =
      -etaCriticalMirrorPairFrameRotatedDefectTail s k := by
  unfold etaCriticalMirrorPairFrameTransportedDefectPartial
  unfold etaCriticalMirrorPairFrameRotatedDefectTail
  rw [etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    hs him (k + 1)]
  ring

/-- Real-part form of the transported-partial tail identity. -/
theorem etaCriticalMirrorPairFrameTransportedDefectPartial_re_eq_neg_rotatedDefectTail_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    (etaCriticalMirrorPairFrameTransportedDefectPartial s k).re =
      -(etaCriticalMirrorPairFrameRotatedDefectTail s k).re := by
  rw [etaCriticalMirrorPairFrameTransportedDefectPartial_eq_neg_rotatedDefectTail
    hs him k]
  simp

/--
Exact sign-reduced form of one sine-transport term.  The eventual coefficient
is positive, so the remaining sign question is the opposite sign of the real
part of the rotated defect tail.
-/
theorem etaCriticalMirrorPairedFrameCorrectionSineTransportTerm_eq_neg_coefficient_mul_rotatedDefectTail_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k =
      -etaCriticalMirrorPairedFrameSineTransportCoefficient s k *
        (etaCriticalMirrorPairFrameRotatedDefectTail s k).re := by
  unfold etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
  unfold etaCriticalMirrorPairedFrameSineTransportCoefficient
  rw [etaCriticalMirrorPairFrameTransportedDefectPartial_re_eq_neg_rotatedDefectTail_re
    hs him k]
  ring

/-- Eventually a positive rotated-tail real part forces a negative sine term. -/
theorem eventually_sineTransportTerm_neg_of_rotatedDefectTail_re_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      0 < (etaCriticalMirrorPairFrameRotatedDefectTail s k).re →
        etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k < 0 := by
  filter_upwards
    [eventually_etaCriticalMirrorPairedFrameSineTransportCoefficient_pos him] with k hcoeff
  intro htail
  rw [etaCriticalMirrorPairedFrameCorrectionSineTransportTerm_eq_neg_coefficient_mul_rotatedDefectTail_re
    hs him k]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcoeff) htail

/-- Eventually a negative rotated-tail real part forces a positive sine term. -/
theorem eventually_sineTransportTerm_pos_of_rotatedDefectTail_re_neg
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      (etaCriticalMirrorPairFrameRotatedDefectTail s k).re < 0 →
        0 < etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k := by
  filter_upwards
    [eventually_etaCriticalMirrorPairedFrameSineTransportCoefficient_pos him] with k hcoeff
  intro htail
  rw [etaCriticalMirrorPairedFrameCorrectionSineTransportTerm_eq_neg_coefficient_mul_rotatedDefectTail_re
    hs him k]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hcoeff) htail

end DkMath.RH.CFBRCProjection
