/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelTailIdentity
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionProjectionTailLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelBalanceAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Successor pair index divided by the current pair index. -/
noncomputable def etaPairSuccessorIndexRatio
    (K : ℕ) : ℝ :=
  (((K + 1 : ℕ) : ℝ)) / (K : ℝ)

/-- The successor/current pair-index ratio tends to one. -/
theorem etaPairSuccessorIndexRatio_tendsto_one :
    Tendsto etaPairSuccessorIndexRatio atTop (nhds 1) := by
  have hinv :
      Tendsto (fun K : ℕ => (1 : ℝ) / (K : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hsum :
      Tendsto
        (fun K : ℕ => (1 : ℝ) + 1 / (K : ℝ))
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  unfold etaPairSuccessorIndexRatio
  change ((K : ℝ) + 1) / (K : ℝ) =
    (1 : ℝ) + 1 / (K : ℝ)
  field_simp [hKpos.ne']

/-- Every fixed real power of the successor/current index ratio tends to one. -/
theorem etaPairSuccessorIndexRatio_rpow_tendsto_one
    (q : ℝ) :
    Tendsto
      (fun K : ℕ => etaPairSuccessorIndexRatio K ^ q)
      atTop (nhds 1) := by
  have h :=
    etaPairSuccessorIndexRatio_tendsto_one.rpow_const
      (p := q) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simpa using h

/-- Right moving-projection constant forced by the normalized Abel balance. -/
noncomputable def etaCriticalMirrorRightNormalizedMovingProjectionTailConstant
    (s : ℂ) : ℝ :=
  -etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s

/-- Left moving-projection constant forced by the normalized Abel balance. -/
noncomputable def etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant
    (s : ℂ) : ℝ :=
  -etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s

/--
Right of the critical line, the successor-index normalized predecessor-frame
whole-tail projection tends to zero.
-/
theorem etaCriticalMirrorRightSuccessorIndexNormalizedPredecessorWholeTailProjection_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s)
      atTop (nhds 0) := by
  have hcomplex :=
    etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant
      hs hre
  have himag :
      Tendsto
        (fun K : ℕ =>
          (((((((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re : ℝ) : ℂ) *
            etaCriticalMirrorPairFrameRotatedDefectTail s K).im))
        atTop (nhds 0) := by
    have h :=
      (Complex.continuous_im.tendsto
        (etaPairIndexNormalizedTailConstant (criticalMirror s))).comp
        hcomplex
    simpa [Function.comp_def, etaPairIndexNormalizedTailConstant_eq_real]
      using h
  have hprojection :
      Tendsto
        (fun K : ℕ =>
          s.im *
            (((((((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re : ℝ) : ℂ) *
              etaCriticalMirrorPairFrameRotatedDefectTail s K).im)))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul himag
  refine hprojection.congr' (Eventually.of_forall fun K => ?_)
  simp [etaCriticalMirrorPredecessorFrameWholeTailProjection,
    etaCriticalMirrorSignedVerticalProjection,
    etaCriticalMirrorPairFrameRotatedDefectTail]
  ring

/--
Left of the critical line, the successor-index normalized predecessor-frame
whole-tail projection tends to zero.
-/
theorem etaCriticalMirrorLeftSuccessorIndexNormalizedPredecessorWholeTailProjection_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ s.re) *
          etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s)
      atTop (nhds 0) := by
  have hcomplex :=
    etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant
      hs hre
  have himag :
      Tendsto
        (fun K : ℕ =>
          (((((((K + 1 : ℕ) : ℝ) ^ s.re : ℝ) : ℂ) *
            etaCriticalMirrorPairFrameRotatedDefectTail s K).im))
        atTop (nhds 0) := by
    have h :=
      (Complex.continuous_im.tendsto
        (-etaPairIndexNormalizedTailConstant s)).comp hcomplex
    simpa [Function.comp_def, etaPairIndexNormalizedTailConstant_eq_real]
      using h
  have hprojection :
      Tendsto
        (fun K : ℕ =>
          s.im *
            (((((((K + 1 : ℕ) : ℝ) ^ s.re : ℝ) : ℂ) *
              etaCriticalMirrorPairFrameRotatedDefectTail s K).im)))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul himag
  refine hprojection.congr' (Eventually.of_forall fun K => ?_)
  simp [etaCriticalMirrorPredecessorFrameWholeTailProjection,
    etaCriticalMirrorSignedVerticalProjection,
    etaCriticalMirrorPairFrameRotatedDefectTail]
  ring

/--
Right correction projection with successor-index normalization has the same
limit as its current-index normalization.
-/
theorem etaCriticalMirrorRightSuccessorIndexNormalizedCorrectionProjectionTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop
      (nhds
        (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s)) := by
  have hratio :=
    etaPairSuccessorIndexRatio_rpow_tendsto_one
      (criticalMirror s).re
  have hindex :=
    etaCriticalMirrorRightNormalizedCorrectionProjectionTail_tendsto_constant
      hs him hre
  have hprod :
      Tendsto
        (fun K : ℕ =>
          etaPairSuccessorIndexRatio K ^ (criticalMirror s).re *
            ((((K : ℝ) ^ (criticalMirror s).re) *
              etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)))
        atTop
        (nhds
          (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s)) := by
    simpa using hratio.mul hindex
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hsuccPos : 0 < (((K + 1 : ℕ) : ℝ)) := by
    positivity
  have hKpow : (K : ℝ) ^ (criticalMirror s).re ≠ 0 :=
    (Real.rpow_pos_of_pos hKpos _).ne'
  unfold etaPairSuccessorIndexRatio
  rw [Real.div_rpow hsuccPos.le hKpos.le]
  field_simp [hKpow]

/--
Left correction projection with successor-index normalization has the same
limit as its current-index normalization.
-/
theorem etaCriticalMirrorLeftSuccessorIndexNormalizedCorrectionProjectionTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop
      (nhds
        (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s)) := by
  have hratio := etaPairSuccessorIndexRatio_rpow_tendsto_one s.re
  have hindex :=
    etaCriticalMirrorLeftNormalizedCorrectionProjectionTail_tendsto_constant
      hs him hre
  have hprod :
      Tendsto
        (fun K : ℕ =>
          etaPairSuccessorIndexRatio K ^ s.re *
            ((((K : ℝ) ^ s.re) *
              etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)))
        atTop
        (nhds
          (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s)) := by
    simpa using hratio.mul hindex
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hsuccPos : 0 < (((K + 1 : ℕ) : ℝ)) := by
    positivity
  have hKpow : (K : ℝ) ^ s.re ≠ 0 :=
    (Real.rpow_pos_of_pos hKpos _).ne'
  unfold etaPairSuccessorIndexRatio
  rw [Real.div_rpow hsuccPos.le hKpos.le]
  field_simp [hKpow]

/-- Exact successor-index normalized Abel balance. -/
theorem etaCriticalMirrorSuccessorIndexNormalizedAbelBalance_eq
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (q : ℝ) (K : ℕ) :
    (((K + 1 : ℕ) : ℝ) ^ q) *
        etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s =
      (((K + 1 : ℕ) : ℝ) ^ q) *
          etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s +
        (((K + 1 : ℕ) : ℝ) ^ q) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s := by
  rw [etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    hs him (K + 1)]
  simp only [Nat.add_sub_cancel]
  ring

/--
Right of the critical line, the moving-frame projection tail carries exactly
the opposite normalized constant to the correction projection tail.
-/
theorem etaCriticalMirrorRightSuccessorIndexNormalizedMovingProjectionTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s)
      atTop
      (nhds
        (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)) := by
  have hwhole :=
    etaCriticalMirrorRightSuccessorIndexNormalizedPredecessorWholeTailProjection_tendsto_zero
      hs hre
  have hcorr :=
    etaCriticalMirrorRightSuccessorIndexNormalizedCorrectionProjectionTail_tendsto_constant
      hs him hre
  have hdiff := hwhole.sub hcorr
  have hlimit :
      Tendsto
        (fun K : ℕ =>
          (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
              etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s -
            (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
              etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
        atTop
        (nhds
          (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)) := by
    simpa [etaCriticalMirrorRightNormalizedMovingProjectionTailConstant]
      using hdiff
  refine hlimit.congr' (Eventually.of_forall fun K => ?_)
  rw [etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    hs him (K + 1)]
  simp only [Nat.add_sub_cancel]
  ring

/--
Left of the critical line, the moving-frame projection tail carries exactly
the opposite normalized constant to the correction projection tail.
-/
theorem etaCriticalMirrorLeftSuccessorIndexNormalizedMovingProjectionTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ s.re) *
          etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s)
      atTop
      (nhds
        (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)) := by
  have hwhole :=
    etaCriticalMirrorLeftSuccessorIndexNormalizedPredecessorWholeTailProjection_tendsto_zero
      hs hre
  have hcorr :=
    etaCriticalMirrorLeftSuccessorIndexNormalizedCorrectionProjectionTail_tendsto_constant
      hs him hre
  have hdiff := hwhole.sub hcorr
  have hlimit :
      Tendsto
        (fun K : ℕ =>
          (((K + 1 : ℕ) : ℝ) ^ s.re) *
              etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s -
            (((K + 1 : ℕ) : ℝ) ^ s.re) *
              etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
        atTop
        (nhds
          (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)) := by
    simpa [etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant]
      using hdiff
  refine hlimit.congr' (Eventually.of_forall fun K => ?_)
  rw [etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    hs him (K + 1)]
  simp only [Nat.add_sub_cancel]
  ring

/-- The normalized right Abel balance tends to zero. -/
theorem etaCriticalMirrorRightSuccessorIndexNormalizedAbelBalance_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s +
          (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop (nhds 0) := by
  have hmove :=
    etaCriticalMirrorRightSuccessorIndexNormalizedMovingProjectionTail_tendsto_constant
      hs him hre
  have hcorr :=
    etaCriticalMirrorRightSuccessorIndexNormalizedCorrectionProjectionTail_tendsto_constant
      hs him hre
  simpa [etaCriticalMirrorRightNormalizedMovingProjectionTailConstant]
    using hmove.add hcorr

/-- The normalized left Abel balance tends to zero. -/
theorem etaCriticalMirrorLeftSuccessorIndexNormalizedAbelBalance_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ s.re) *
            etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s +
          (((K + 1 : ℕ) : ℝ) ^ s.re) *
            etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop (nhds 0) := by
  have hmove :=
    etaCriticalMirrorLeftSuccessorIndexNormalizedMovingProjectionTail_tendsto_constant
      hs him hre
  have hcorr :=
    etaCriticalMirrorLeftSuccessorIndexNormalizedCorrectionProjectionTail_tendsto_constant
      hs him hre
  simpa [etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant]
    using hmove.add hcorr

/-- The right moving-projection constant is strictly positive. -/
theorem etaCriticalMirrorRightNormalizedMovingProjectionTailConstant_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s := by
  unfold etaCriticalMirrorRightNormalizedMovingProjectionTailConstant
  exact neg_pos.mpr
    (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant_neg
      hs him)

/-- The left moving-projection constant is strictly negative. -/
theorem etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant_neg
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s < 0 := by
  unfold etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant
  exact neg_neg_of_pos
    (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant_pos
      hs him)

/-- Right-side nonzero constants cancel exactly in the normalized Abel balance. -/
theorem etaCriticalMirrorRightNormalizedAbelBalance_nonzero_cancellation
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s ∧
      etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s < 0 ∧
      etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s +
          etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s = 0 := by
  refine ⟨etaCriticalMirrorRightNormalizedMovingProjectionTailConstant_pos hs him,
    etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant_neg hs him, ?_⟩
  unfold etaCriticalMirrorRightNormalizedMovingProjectionTailConstant
  ring

/-- Left-side nonzero constants cancel exactly in the normalized Abel balance. -/
theorem etaCriticalMirrorLeftNormalizedAbelBalance_nonzero_cancellation
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s < 0 ∧
      0 < etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s ∧
      etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s +
          etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s = 0 := by
  refine ⟨etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant_neg hs him,
    etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant_pos hs him, ?_⟩
  unfold etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant
  ring

end DkMath.RH.CFBRCProjection
