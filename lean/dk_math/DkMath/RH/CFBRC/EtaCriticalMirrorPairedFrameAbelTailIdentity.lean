/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjectionTail
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelTailIdentity"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Complex moving-frame defect tail beginning at pair index `K`. -/
noncomputable def etaCriticalMirrorRotatedDefectPairTail
    (K : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ,
    etaCriticalMirrorRotatedDefectPairTerm s (n + K)

/-- Complex Abel frame-correction tail beginning at correction index `K`. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionTail
    (K : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ,
    etaCriticalMirrorPairedFrameCorrectionTerm s (n + K)

/-- Signed vertical projection of the preceding Abel correction tail. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionProjectionTail
    (K : ℕ) (s : ℂ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorPairedFrameCorrectionTail K s)

/--
Projection of the ordinary paired tail in the frame immediately preceding its
first pair-left frame.
-/
noncomputable def etaCriticalMirrorPredecessorFrameWholeTailProjection
    (K : ℕ) (s : ℂ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaPairBaseRotation s (K - 1) *
      etaCriticalMirrorDefectPairTail K s)

/-- Pair-local rotations preserve the summability of the complex defect series. -/
theorem summable_etaCriticalMirrorRotatedDefectPairTerm
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Summable (etaCriticalMirrorRotatedDefectPairTerm s) := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  refine
    Summable.of_norm_bounded
      (summable_etaCriticalMirrorDefectPairMajorant hsre hmre) ?_
  intro k
  unfold etaCriticalMirrorRotatedDefectPairTerm
  rw [norm_mul, norm_etaPairBaseRotation, one_mul]
  exact norm_etaCriticalMirrorDefectPairTerm_le_majorant hsre hmre k

/-- The complex moving-frame defect tail is summable after every prefix. -/
theorem summable_etaCriticalMirrorRotatedDefectPairTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (K : ℕ) :
    Summable
      (fun n : ℕ =>
        etaCriticalMirrorRotatedDefectPairTerm s (n + K)) :=
  (summable_nat_add_iff K).2
    (summable_etaCriticalMirrorRotatedDefectPairTerm hs)

/-- The complex Abel correction tail is summable after every prefix. -/
theorem summable_etaCriticalMirrorPairedFrameCorrectionTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    Summable
      (fun n : ℕ =>
        etaCriticalMirrorPairedFrameCorrectionTerm s (n + K)) :=
  (summable_nat_add_iff K).2
    (summable_etaCriticalMirrorPairedFrameCorrectionTerm_of_nontrivialRiemannZetaZero
      hs him)

/--
The complete complex moving-frame defect sum is the negative complete Abel
correction sum.
-/
theorem tsum_etaCriticalMirrorRotatedDefectPairTerm_eq_neg_correction_tsum
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    (∑' k : ℕ, etaCriticalMirrorRotatedDefectPairTerm s k) =
      -(∑' k : ℕ,
        etaCriticalMirrorPairedFrameCorrectionTerm s k) := by
  have hsum := summable_etaCriticalMirrorRotatedDefectPairTerm hs
  have htsum :
      Tendsto
        (fun K : ℕ => etaCriticalMirrorRotatedDefectPairedPartial K s)
        atTop
        (nhds
          (∑' k : ℕ,
            etaCriticalMirrorRotatedDefectPairTerm s k)) := by
    simpa [etaCriticalMirrorRotatedDefectPairedPartial] using
      hsum.hasSum.tendsto_sum_nat
  exact
    tendsto_nhds_unique htsum
      (etaCriticalMirrorRotatedDefectPairedPartial_tendsto_neg_correction_tsum
        hs him)

/--
Infinite tail form of the Abel transformation.

The ordinary defect tail in the predecessor pair frame equals the moving-frame
defect tail plus the remaining frame-correction tail.
-/
theorem etaPairBaseRotation_pred_mul_defectPairTail_eq_rotatedTail_add_correctionTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaPairBaseRotation s (K - 1) *
        etaCriticalMirrorDefectPairTail K s =
      etaCriticalMirrorRotatedDefectPairTail K s +
        etaCriticalMirrorPairedFrameCorrectionTail (K - 1) s := by
  have hrot := summable_etaCriticalMirrorRotatedDefectPairTerm hs
  have hcorr :=
    summable_etaCriticalMirrorPairedFrameCorrectionTerm_of_nontrivialRiemannZetaZero
      hs him
  have hrotSplit := hrot.sum_add_tsum_nat_add K
  have hcorrSplit := hcorr.sum_add_tsum_nat_add (K - 1)
  have habel :=
    etaCriticalMirrorRotatedDefectPairedPartial_eq_abel K s
  have hpartial :=
    etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him K
  have htotal :=
    tsum_etaCriticalMirrorRotatedDefectPairTerm_eq_neg_correction_tsum
      hs him
  unfold etaCriticalMirrorRotatedDefectPairedPartial at habel
  unfold etaCriticalMirrorPairedAbelBoundaryTerm at habel
  rw [hpartial] at habel
  unfold etaCriticalMirrorRotatedDefectPairTail
  unfold etaCriticalMirrorPairedFrameCorrectionTail
  rw [htotal] at hrotSplit
  linear_combination -(hrotSplit) - hcorrSplit + habel

/--
Projection of the complex moving-frame tail equals the previously named real
projection tail.
-/
theorem etaCriticalMirrorSignedVerticalProjection_rotatedTail_eq_projectionTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (K : ℕ) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorRotatedDefectPairTail K s) =
      etaCriticalMirrorRotatedDefectProjectionTail K s := by
  have hsum :=
    summable_etaCriticalMirrorRotatedDefectPairTail hs K
  have himag :
      HasSum
        (fun n : ℕ =>
          (etaCriticalMirrorRotatedDefectPairTerm s (n + K)).im)
        ((etaCriticalMirrorRotatedDefectPairTail K s).im) := by
    unfold etaCriticalMirrorRotatedDefectPairTail
    simpa using hsum.hasSum.map Complex.imCLM
  have hscaled := himag.mul_left s.im
  unfold etaCriticalMirrorSignedVerticalProjection
  unfold etaCriticalMirrorRotatedDefectProjectionTail
  unfold etaCriticalMirrorRotatedDefectPairProjection
  exact hscaled.tsum_eq.symm

/--
Signed projection form of the infinite Abel tail identity.
-/
theorem etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPredecessorFrameWholeTailProjection K s =
      etaCriticalMirrorRotatedDefectProjectionTail K s +
        etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s := by
  unfold etaCriticalMirrorPredecessorFrameWholeTailProjection
  unfold etaCriticalMirrorPairedFrameCorrectionProjectionTail
  rw [etaPairBaseRotation_pred_mul_defectPairTail_eq_rotatedTail_add_correctionTail
    hs him K]
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [Complex.add_im, mul_add]
  rw [etaCriticalMirrorSignedVerticalProjection_rotatedTail_eq_projectionTail
    hs K]

end DkMath.RH.CFBRCProjection
