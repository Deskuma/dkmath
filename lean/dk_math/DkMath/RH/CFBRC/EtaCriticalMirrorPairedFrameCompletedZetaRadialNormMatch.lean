/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialTransverseDecomposition
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialNormMatch"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Positive real radius of the normalized eta half-tail constant. -/
noncomputable def etaPairIndexNormalizedTailRadius
    (z : ℂ) : ℝ :=
  ((1 : ℝ) / 2) * (((1 : ℝ) / 2) ^ z.re)

/-- The complex eta half-tail constant has the explicit positive radius. -/
theorem norm_etaPairIndexNormalizedTailConstant_eq_radius
    (z : ℂ) :
    ‖etaPairIndexNormalizedTailConstant z‖ =
      etaPairIndexNormalizedTailRadius z := by
  simp [etaPairIndexNormalizedTailConstant,
    etaPairIndexNormalizedTailRadius, Real.rpow_nonneg]

/-- The normalized eta half-tail radius is nonnegative. -/
theorem etaPairIndexNormalizedTailRadius_nonneg
    (z : ℂ) :
    0 ≤ etaPairIndexNormalizedTailRadius z := by
  unfold etaPairIndexNormalizedTailRadius
  positivity

/-- On the left side, the explicit radial amplitude tends to the negative eta radius. -/
theorem etaCriticalMirrorDominantRadialAmplitude_tendsto_neg_radius_of_left
    {s : ℂ} (hleft : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ => etaCriticalMirrorDominantRadialAmplitude k s)
      atTop (nhds (-etaPairIndexNormalizedTailRadius s)) := by
  have hratio :=
    etaPairIndexToSuccessorEndpointRatio_tendsto_half.rpow_const
      (p := s.re) (Or.inl (by norm_num : ((1 : ℝ) / 2) ≠ 0))
  have hscaled :
      Tendsto
        (fun k : ℕ =>
          ((1 : ℝ) / 2) *
            (etaPairIndexToSuccessorEndpointRatio k ^ s.re))
        atTop
        (nhds
          (((1 : ℝ) / 2) * (((1 : ℝ) / 2) ^ s.re))) := by
    simpa using
      (show Tendsto (fun _ : ℕ => (1 : ℝ) / 2) atTop
          (nhds ((1 : ℝ) / 2)) from tendsto_const_nhds).mul hratio
  have hneg :
      Tendsto
        (fun k : ℕ => (-((1 : ℝ) / 2)) *
          (etaPairIndexToSuccessorEndpointRatio k ^ s.re))
        atTop
        (nhds ((-((1 : ℝ) / 2)) * (((1 : ℝ) / 2) ^ s.re))) := by
    exact
      (show Tendsto (fun _ : ℕ => (-((1 : ℝ) / 2))) atTop
          (nhds (-((1 : ℝ) / 2))) from tendsto_const_nhds).mul hratio
  have hle : s.re ≤ (1 : ℝ) / 2 := le_of_lt hleft
  have hle' : s.re ≤ 2⁻¹ := by simpa using hle
  simpa [etaCriticalMirrorDominantRadialAmplitude,
    etaPairIndexNormalizedTailRadius, hle, hle'] using hneg

/-- On the right side, the explicit radial amplitude tends to the mirror eta radius. -/
theorem etaCriticalMirrorDominantRadialAmplitude_tendsto_radius_of_right
    {s : ℂ} (hright : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ => etaCriticalMirrorDominantRadialAmplitude k s)
      atTop
      (nhds (etaPairIndexNormalizedTailRadius (criticalMirror s))) := by
  have hratio :=
    etaPairIndexToSuccessorEndpointRatio_tendsto_half.rpow_const
      (p := (criticalMirror s).re)
      (Or.inl (by norm_num : ((1 : ℝ) / 2) ≠ 0))
  have hscaled :
      Tendsto
        (fun k : ℕ =>
          ((1 : ℝ) / 2) *
            (etaPairIndexToSuccessorEndpointRatio k ^
              (criticalMirror s).re))
        atTop
        (nhds
          (((1 : ℝ) / 2) *
            (((1 : ℝ) / 2) ^ (criticalMirror s).re))) := by
    simpa using
      (show Tendsto (fun _ : ℕ => (1 : ℝ) / 2) atTop
          (nhds ((1 : ℝ) / 2)) from tendsto_const_nhds).mul hratio
  have hnotle : ¬ s.re ≤ (1 : ℝ) / 2 := not_le.mpr hright
  have hnotle' : ¬ s.re ≤ 2⁻¹ := by simpa using hnotle
  simpa [etaCriticalMirrorDominantRadialAmplitude,
    etaPairIndexNormalizedTailRadius, hnotle, hnotle'] using hscaled

/-- The left radial-ray model norm tends to the same eta radius as the endpoint norm. -/
theorem norm_etaCriticalMirrorCompletedZetaDominantRadialRayModel_tendsto_left
    {s : ℂ} (hleft : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorCompletedZetaDominantRadialRayModel k s‖)
      atTop (nhds ‖etaPairIndexNormalizedTailConstant s‖) := by
  have hamp :=
    etaCriticalMirrorDominantRadialAmplitude_tendsto_neg_radius_of_left hleft
  have habs0 :=
    (continuous_norm.tendsto (-etaPairIndexNormalizedTailRadius s)).comp hamp
  have habs :
      Tendsto
        (fun k : ℕ =>
          |etaCriticalMirrorDominantRadialAmplitude k s|)
        atTop (nhds (etaPairIndexNormalizedTailRadius s)) := by
    simpa [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (etaPairIndexNormalizedTailRadius_nonneg s)] using habs0
  rw [norm_etaPairIndexNormalizedTailConstant_eq_radius]
  refine habs.congr' (Eventually.of_forall fun k => ?_)
  simp [etaCriticalMirrorCompletedZetaDominantRadialRayModel,
    completedZetaCanonicalSlopeRayModel, norm_completedZetaCanonicalSlopeUnitDirection]

/-- The right radial-ray model norm tends to the same mirror eta radius as the endpoint norm. -/
theorem norm_etaCriticalMirrorCompletedZetaDominantRadialRayModel_tendsto_right
    {s : ℂ} (hright : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorCompletedZetaDominantRadialRayModel k s‖)
      atTop
      (nhds ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖) := by
  have hamp :=
    etaCriticalMirrorDominantRadialAmplitude_tendsto_radius_of_right hright
  have habs0 :=
    (continuous_norm.tendsto
      (etaPairIndexNormalizedTailRadius (criticalMirror s))).comp hamp
  have habs :
      Tendsto
        (fun k : ℕ =>
          |etaCriticalMirrorDominantRadialAmplitude k s|)
        atTop
        (nhds (etaPairIndexNormalizedTailRadius (criticalMirror s))) := by
    simpa [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg
        (etaPairIndexNormalizedTailRadius_nonneg (criticalMirror s))] using habs0
  rw [norm_etaPairIndexNormalizedTailConstant_eq_radius]
  refine habs.congr' (Eventually.of_forall fun k => ?_)
  simp [etaCriticalMirrorCompletedZetaDominantRadialRayModel,
    completedZetaCanonicalSlopeRayModel, norm_completedZetaCanonicalSlopeUnitDirection]

/--
At every nonreal off-critical zero, endpoint norm and explicit ray-model norm
have the same nonzero asymptotic radius.
-/
theorem etaCriticalMirrorDominantEndpoint_sub_rayModel_norm_tendsto_zero_of_offCriticalZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖ -
          ‖etaCriticalMirrorCompletedZetaDominantRadialRayModel k s‖)
      atTop (nhds 0) := by
  rcases lt_or_gt_of_ne hre with hleft | hright
  · have hendpoint :=
      (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hleft).endpoint_norm_tendsto
    have hendpoint' :
        Tendsto
          (fun k : ℕ =>
            ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖)
          atTop (nhds ‖etaPairIndexNormalizedTailConstant s‖) := by
      have hle : s.re ≤ (1 : ℝ) / 2 := le_of_lt hleft
      have hle' : s.re ≤ 2⁻¹ := by simpa using hle
      simpa [etaCriticalMirrorDominantNormalizedEndpointCarrier,
        hle, hle', norm_neg] using hendpoint
    have hmodel :=
      norm_etaCriticalMirrorCompletedZetaDominantRadialRayModel_tendsto_left
        hleft
    simpa using hendpoint'.sub hmodel
  · have hendpoint :=
      (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hright).endpoint_norm_tendsto
    have hendpoint' :
        Tendsto
          (fun k : ℕ =>
            ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖)
          atTop
          (nhds ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖) := by
      have hnotle : ¬ s.re ≤ (1 : ℝ) / 2 := not_le.mpr hright
      have hnotle' : ¬ s.re ≤ 2⁻¹ := by simpa using hnotle
      simpa [etaCriticalMirrorDominantNormalizedEndpointCarrier,
        hnotle, hnotle'] using hendpoint
    have hmodel :=
      norm_etaCriticalMirrorCompletedZetaDominantRadialRayModel_tendsto_right
        hright
    simpa using hendpoint'.sub hmodel

#print axioms etaCriticalMirrorDominantRadialAmplitude_tendsto_neg_radius_of_left
#print axioms etaCriticalMirrorDominantRadialAmplitude_tendsto_radius_of_right
#print axioms etaCriticalMirrorDominantEndpoint_sub_rayModel_norm_tendsto_zero_of_offCriticalZero

end DkMath.RH.CFBRCProjection
