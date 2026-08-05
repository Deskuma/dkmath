/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
Gauge-invariant chord between two index-normalized unrotated defect tails.
A common unit rotation applied to both endpoints leaves this norm unchanged.
-/
noncomputable def etaCriticalMirrorIndexNormalizedDefectTailChord
    (a : ℝ) (s : ℂ) (K N : ℕ) : ℝ :=
  ‖etaCriticalMirrorIndexNormalizedDefectTail a s (K + N) -
    etaCriticalMirrorIndexNormalizedDefectTail a s K‖

/--
The unrotated normalized-tail chord is exactly the chord between the terminal
rotated tail and the initial rotated tail transported by the relative frame
rotation.
-/
theorem etaCriticalMirrorIndexNormalizedDefectTailChord_eq_rotated_sub_blockRotation_mul
    (a : ℝ) (s : ℂ) (K N : ℕ) :
    etaCriticalMirrorIndexNormalizedDefectTailChord a s K N =
      ‖etaCriticalMirrorIndexNormalizedRotatedDefectTail a s (K + N) -
        etaPairFrameBlockRotation s K N *
          etaCriticalMirrorIndexNormalizedRotatedDefectTail a s K‖ := by
  unfold etaCriticalMirrorIndexNormalizedDefectTailChord
  rw [etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul,
    etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul,
    etaPairBaseRotation_add_eq_mul_blockRotation]
  have hfactor :
      (etaPairBaseRotation s K * etaPairFrameBlockRotation s K N) *
          etaCriticalMirrorIndexNormalizedDefectTail a s (K + N) -
        etaPairFrameBlockRotation s K N *
          (etaPairBaseRotation s K *
            etaCriticalMirrorIndexNormalizedDefectTail a s K) =
        (etaPairBaseRotation s K * etaPairFrameBlockRotation s K N) *
          (etaCriticalMirrorIndexNormalizedDefectTail a s (K + N) -
            etaCriticalMirrorIndexNormalizedDefectTail a s K) := by
    ring
  rw [hfactor, norm_mul, norm_mul, norm_etaPairBaseRotation,
    norm_etaPairFrameBlockRotation, one_mul, one_mul]

namespace EtaPairPositiveDensityBlockSchedule

/-- The normalized-tail chord sampled along one positive-density schedule. -/
noncomputable def scheduledNormalizedDefectTailChord
    (S : EtaPairPositiveDensityBlockSchedule)
    (a : ℝ) (s : ℂ) (K : ℕ) : ℝ :=
  etaCriticalMirrorIndexNormalizedDefectTailChord
    a s K (S.blockLength K)

/-- Every terminal index `K + blockLength K` is cofinal at `atTop`. -/
private theorem terminalIndex_tendsto_atTop
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto (fun K : ℕ => K + S.blockLength K) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro K hK
    omega⟩

/--
If the normalized rotated defect tail tends to `C`, then the gauge-invariant
scheduled unrotated chord has the explicit relative-rotation limit.
-/
theorem scheduledNormalizedDefectTailChord_tendsto
    (S : EtaPairPositiveDensityBlockSchedule)
    {a : ℝ} {s C : ℂ}
    (hrotated :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail a s)
        atTop (nhds C)) :
    Tendsto
      (S.scheduledNormalizedDefectTailChord a s)
      atTop
      (nhds
        ‖C - S.scheduledBlockRotationLimit s * C‖) := by
  have hterminal :
      Tendsto
        (fun K : ℕ =>
          etaCriticalMirrorIndexNormalizedRotatedDefectTail
            a s (K + S.blockLength K))
        atTop (nhds C) :=
    hrotated.comp S.terminalIndex_tendsto_atTop
  have htransport :
      Tendsto
        (fun K : ℕ =>
          S.scheduledBlockRotation s K *
            etaCriticalMirrorIndexNormalizedRotatedDefectTail a s K)
        atTop
        (nhds (S.scheduledBlockRotationLimit s * C)) :=
    (S.scheduledBlockRotation_tendsto s).mul hrotated
  have hdiff :
      Tendsto
        (fun K : ℕ =>
          etaCriticalMirrorIndexNormalizedRotatedDefectTail
              a s (K + S.blockLength K) -
            S.scheduledBlockRotation s K *
              etaCriticalMirrorIndexNormalizedRotatedDefectTail a s K)
        atTop
        (nhds (C - S.scheduledBlockRotationLimit s * C)) :=
    hterminal.sub htransport
  have hnorm :
      Tendsto
        (fun K : ℕ =>
          ‖etaCriticalMirrorIndexNormalizedRotatedDefectTail
              a s (K + S.blockLength K) -
            S.scheduledBlockRotation s K *
              etaCriticalMirrorIndexNormalizedRotatedDefectTail a s K‖)
        atTop
        (nhds ‖C - S.scheduledBlockRotationLimit s * C‖) := by
    change Tendsto
      ((fun z : ℂ => ‖z‖) ∘
        (fun K : ℕ =>
          etaCriticalMirrorIndexNormalizedRotatedDefectTail
              a s (K + S.blockLength K) -
            S.scheduledBlockRotation s K *
              etaCriticalMirrorIndexNormalizedRotatedDefectTail a s K))
      atTop
      (nhds ‖C - S.scheduledBlockRotationLimit s * C‖)
    simpa only [Function.comp_apply] using
      (continuous_norm.tendsto
        (C - S.scheduledBlockRotationLimit s * C)).comp hdiff
  refine hnorm.congr' (Eventually.of_forall fun K => ?_)
  simpa [scheduledNormalizedDefectTailChord, scheduledBlockRotation] using
    (etaCriticalMirrorIndexNormalizedDefectTailChord_eq_rotated_sub_blockRotation_mul
      a s K (S.blockLength K)).symm

end EtaPairPositiveDensityBlockSchedule

/-- A nontrivial relative rotation and a nonzero tail constant give a nonzero chord limit. -/
theorem norm_constant_sub_rotation_mul_ne_zero
    {C Q : ℂ} (hC : C ≠ 0) (hQ : Q ≠ 1) :
    ‖C - Q * C‖ ≠ 0 := by
  apply norm_ne_zero_iff.mpr
  rw [show C - Q * C = (1 - Q) * C by ring]
  exact mul_ne_zero (sub_ne_zero.mpr hQ.symm) hC

/--
Certificate recording the two gauge-invariant normalized-tail chord limits and
that at least one of them is nonzero.
-/
structure EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
    (a : ℝ) (s C : ℂ) : Prop where
  halfDensityChord_tendsto :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledNormalizedDefectTailChord a s)
      atTop
      (nhds
        ‖C -
          etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s * C‖)
  fullDensityChord_tendsto :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledNormalizedDefectTailChord a s)
      atTop
      (nhds
        ‖C -
          etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s * C‖)
  at_least_one_chord_limit_ne_zero :
    ‖C -
        etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s * C‖ ≠ 0 ∨
      ‖C -
        etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s * C‖ ≠ 0

/-- A nonzero rotated-tail limit at a nonreal point yields the two-scale chord certificate. -/
theorem etaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate_of_rotated_limit
    {a : ℝ} {s C : ℂ}
    (him : s.im ≠ 0)
    (hrotated :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail a s)
        atTop (nhds C))
    (hC : C ≠ 0) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate a s C := by
  refine ⟨
    etaPairHalfDensityBlockSchedule.scheduledNormalizedDefectTailChord_tendsto
      hrotated,
    etaPairFullDensityBlockSchedule.scheduledNormalizedDefectTailChord_tendsto
      hrotated,
    ?_⟩
  rcases etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_ne_one him with
      hhalf | hfull
  · exact Or.inl (norm_constant_sub_rotation_mul_ne_zero hC hhalf)
  · exact Or.inr (norm_constant_sub_rotation_mul_ne_zero hC hfull)

/-- Right of the critical line, the dominant normalized defect tail has a nontrivial two-scale chord. -/
theorem etaCriticalMirrorRightTwoScaleNormalizedDefectTailChordCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
      (criticalMirror s).re s
      (etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  apply
    etaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate_of_rotated_limit
      him
  · convert
      etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant
        hs hre using 1
    rfl
  · exact etaPairIndexNormalizedTailConstant_ne_zero (criticalMirror s)

/-- Left of the critical line, the dominant normalized defect tail has a nontrivial two-scale chord. -/
theorem etaCriticalMirrorLeftTwoScaleNormalizedDefectTailChordCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
      s.re s (-etaPairIndexNormalizedTailConstant s) := by
  apply
    etaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate_of_rotated_limit
      him
  · convert
      etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant
        hs hre using 1
    rfl
  · exact neg_ne_zero.mpr (etaPairIndexNormalizedTailConstant_ne_zero s)

/--
Every nonreal off-critical nontrivial zero carries a gauge-invariant two-scale
normalized-defect-tail chord certificate on its dominant side.
-/
theorem etaCriticalMirrorOffCriticalTwoScaleNormalizedDefectTailChordCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    (s.re < (1 : ℝ) / 2 ∧
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
        s.re s (-etaPairIndexNormalizedTailConstant s)) ∨
    ((1 : ℝ) / 2 < s.re ∧
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
        (criticalMirror s).re s
        (etaPairIndexNormalizedTailConstant (criticalMirror s))) := by
  rcases lt_or_gt_of_ne hre with hleft | hright
  · exact Or.inl
      ⟨hleft,
        etaCriticalMirrorLeftTwoScaleNormalizedDefectTailChordCertificate_of_zero
          hs him hleft⟩
  · exact Or.inr
      ⟨hright,
        etaCriticalMirrorRightTwoScaleNormalizedDefectTailChordCertificate_of_zero
          hs him hright⟩

end DkMath.RH.CFBRCProjection
