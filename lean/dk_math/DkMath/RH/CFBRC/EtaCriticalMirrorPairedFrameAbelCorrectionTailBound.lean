/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelTailIdentity
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelCorrectionTailBound"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Explicit p-series bound for the complex Abel correction tail from `K`. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionTailPowerBound
    (s : ℂ) (K : ℕ) : ℝ :=
  (4 * |s.im| / (criticalMirror s).re) *
      (‖criticalMirror s‖ *
        (((K : ℝ) ^ (-(criticalMirror s).re)) /
          (criticalMirror s).re)) +
    (4 * |s.im| / s.re) *
      (‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re))

/-- Explicit bound for the signed projection of the Abel correction tail. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
    (s : ℂ) (K : ℕ) : ℝ :=
  |s.im| * etaCriticalMirrorPairedFrameCorrectionTailPowerBound s K

/-- The shifted correction majorant `tsum` obeys the named power bound. -/
theorem tsum_etaCriticalMirrorPairedFrameCorrectionMajorant_nat_add_le_powerBound
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑' n : ℕ,
      etaCriticalMirrorPairedFrameCorrectionMajorant s (n + K)) ≤
      etaCriticalMirrorPairedFrameCorrectionTailPowerBound s K := by
  let A : ℝ := 4 * |s.im| / (criticalMirror s).re
  let B : ℝ := 4 * |s.im| / s.re
  have hMirrorTail := shifted_rpow_tail_le hm hK
  have hOriginalTail := shifted_rpow_tail_le hs hK
  have hMirrorSummable :
      Summable
        (fun n : ℕ =>
          (((n + K + 1 : ℕ) : ℝ) ^
            (-(criticalMirror s).re - 1))) := by
    have h := summable_etaPairMajorant hm
    by_cases hzero : ‖criticalMirror s‖ = 0
    · have : criticalMirror s = 0 := norm_eq_zero.mp hzero
      simp [this] at hm
    · exact
        (summable_mul_left_iff hzero).1
          (by simpa [Nat.add_assoc] using
            (summable_nat_add_iff K).2 h)
  have hOriginalSummable :
      Summable
        (fun n : ℕ =>
          (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1))) := by
    have h := summable_etaPairMajorant hs
    have hzero : ‖s‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (by
        intro hs0
        simp [hs0] at hs)
    exact
      (summable_mul_left_iff hzero).1
        (by simpa [Nat.add_assoc] using
          (summable_nat_add_iff K).2 h)
  have hMirrorScaled :
      Summable
        (fun n : ℕ =>
          A *
            (‖criticalMirror s‖ *
              (((n + K + 1 : ℕ) : ℝ) ^
                (-(criticalMirror s).re - 1)))) :=
    (hMirrorSummable.mul_left ‖criticalMirror s‖).mul_left A
  have hOriginalScaled :
      Summable
        (fun n : ℕ =>
          B *
            (‖s‖ *
              (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1)))) :=
    (hOriginalSummable.mul_left ‖s‖).mul_left B
  have hMirrorFactor :
      (∑' n : ℕ,
        A *
          (‖criticalMirror s‖ *
            (((n + K + 1 : ℕ) : ℝ) ^
              (-(criticalMirror s).re - 1)))) =
        A *
          (‖criticalMirror s‖ *
            (∑' n : ℕ,
              (((n + K + 1 : ℕ) : ℝ) ^
                (-(criticalMirror s).re - 1)))) :=
    ((hMirrorSummable.hasSum.mul_left ‖criticalMirror s‖).mul_left A).tsum_eq
  have hOriginalFactor :
      (∑' n : ℕ,
        B *
          (‖s‖ *
            (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1)))) =
        B *
          (‖s‖ *
            (∑' n : ℕ,
              (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1)))) :=
    ((hOriginalSummable.hasSum.mul_left ‖s‖).mul_left B).tsum_eq
  have hAdd :=
    (hMirrorScaled.hasSum.add hOriginalScaled.hasSum).tsum_eq
  have hmajorantTsum :
      (∑' n : ℕ,
        etaCriticalMirrorPairedFrameCorrectionMajorant s (n + K)) =
        A *
            (‖criticalMirror s‖ *
              (∑' n : ℕ,
                (((n + K + 1 : ℕ) : ℝ) ^
                  (-(criticalMirror s).re - 1)))) +
          B *
            (‖s‖ *
              (∑' n : ℕ,
                (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1)))) := by
    unfold etaCriticalMirrorPairedFrameCorrectionMajorant
    change
      (∑' n : ℕ,
        A *
            (‖criticalMirror s‖ *
              (((n + K + 1 : ℕ) : ℝ) ^
                (-(criticalMirror s).re - 1))) +
          B *
            (‖s‖ *
              (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1)))) = _
    rw [hAdd, hMirrorFactor, hOriginalFactor]
  rw [hmajorantTsum]
  unfold etaCriticalMirrorPairedFrameCorrectionTailPowerBound
  change
    A *
          (‖criticalMirror s‖ *
            (∑' n : ℕ,
              (((n + K + 1 : ℕ) : ℝ) ^
                (-(criticalMirror s).re - 1)))) +
        B *
          (‖s‖ *
            (∑' n : ℕ,
              (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 1))) ≤
      A *
          (‖criticalMirror s‖ *
            (((K : ℝ) ^ (-(criticalMirror s).re)) /
              (criticalMirror s).re)) +
        B *
          (‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re))
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hMirrorTail (norm_nonneg _))
      (by dsimp [A]; positivity))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hOriginalTail (norm_nonneg _))
      (by dsimp [B]; positivity))

/-- The complex Abel correction tail eventually obeys its explicit power bound. -/
theorem eventually_norm_etaCriticalMirrorPairedFrameCorrectionTail_le_powerBound
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      ‖etaCriticalMirrorPairedFrameCorrectionTail K s‖ ≤
        etaCriticalMirrorPairedFrameCorrectionTailPowerBound s K := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  rcases eventually_atTop.1
      (eventually_norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
        hs him) with ⟨K0, hK0⟩
  filter_upwards [eventually_ge_atTop (max 1 K0)] with K hK
  have hKone : 1 ≤ K := by omega
  have hMajorantShift :
      Summable
        (fun n : ℕ =>
          etaCriticalMirrorPairedFrameCorrectionMajorant s (n + K)) :=
    (summable_nat_add_iff K).2
      (summable_etaCriticalMirrorPairedFrameCorrectionMajorant hsre hmre)
  have hnorm :
      ‖etaCriticalMirrorPairedFrameCorrectionTail K s‖ ≤
        ∑' n : ℕ,
          etaCriticalMirrorPairedFrameCorrectionMajorant s (n + K) := by
    unfold etaCriticalMirrorPairedFrameCorrectionTail
    exact
      tsum_of_norm_bounded hMajorantShift.hasSum
        (fun n => hK0 (n + K) (by omega))
  exact hnorm.trans
    (tsum_etaCriticalMirrorPairedFrameCorrectionMajorant_nat_add_le_powerBound
      hsre hmre hKone)

/-- Signed projection never exceeds `|s.im|` times the complex correction-tail norm. -/
theorem abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le
    (s : ℂ) (K : ℕ) :
    |etaCriticalMirrorPairedFrameCorrectionProjectionTail K s| ≤
      |s.im| * ‖etaCriticalMirrorPairedFrameCorrectionTail K s‖ := by
  unfold etaCriticalMirrorPairedFrameCorrectionProjectionTail
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [abs_mul]
  exact
    mul_le_mul_of_nonneg_left
      (Complex.abs_im_le_norm
        (etaCriticalMirrorPairedFrameCorrectionTail K s))
      (abs_nonneg s.im)

/-- The correction projection tail eventually obeys the named explicit bound. -/
theorem eventually_abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le_powerBound
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      |etaCriticalMirrorPairedFrameCorrectionProjectionTail K s| ≤
        etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K := by
  filter_upwards
    [eventually_norm_etaCriticalMirrorPairedFrameCorrectionTail_le_powerBound
      hs him] with K hK
  unfold etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
  exact
    (abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le s K).trans
      (mul_le_mul_of_nonneg_left hK (abs_nonneg s.im))

/-- Right-side condition that the correction bound is below the moving projection tail. -/
def RightAbelCorrectionTailDominated
    (s : ℂ) : Prop :=
  ∀ᶠ K : ℕ in atTop,
    etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s (K - 1) <
      etaCriticalMirrorRotatedDefectProjectionTail K s

/-- Left-side condition that the correction bound is below the negated moving projection tail. -/
def LeftAbelCorrectionTailDominated
    (s : ℂ) : Prop :=
  ∀ᶠ K : ℕ in atTop,
    etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s (K - 1) <
      -etaCriticalMirrorRotatedDefectProjectionTail K s

/-- Right correction domination forces the predecessor-frame whole tail positive. -/
theorem eventually_predecessorFrameWholeTailProjection_pos_of_rightAbelCorrectionTailDominated
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : RightAbelCorrectionTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorPredecessorFrameWholeTailProjection K s := by
  have hcorr :=
    eventually_abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le_powerBound
      hs him
  have hcorrPred :
      ∀ᶠ K : ℕ in atTop,
        |etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s| ≤
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s (K - 1) :=
    hcorr.comp_tendsto tendsto_nat_pred_atTop
  have htail :=
    eventually_etaCriticalMirrorRotatedDefectProjectionTail_pos_of_half_lt_re
      hs him hre
  filter_upwards [hcorrPred, htail, hdom] with K hcorrK htailK hdomK
  have habs :
      |etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s| <
        etaCriticalMirrorRotatedDefectProjectionTail K s :=
    hcorrK.trans_lt hdomK
  have hlower := neg_lt_of_abs_lt habs
  rw [etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    hs him K]
  linarith

/-- Left correction domination forces the predecessor-frame whole tail negative. -/
theorem eventually_predecessorFrameWholeTailProjection_neg_of_leftAbelCorrectionTailDominated
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : LeftAbelCorrectionTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPredecessorFrameWholeTailProjection K s < 0 := by
  have hcorr :=
    eventually_abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le_powerBound
      hs him
  have hcorrPred :
      ∀ᶠ K : ℕ in atTop,
        |etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s| ≤
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s (K - 1) :=
    hcorr.comp_tendsto tendsto_nat_pred_atTop
  have htail :=
    eventually_etaCriticalMirrorRotatedDefectProjectionTail_neg_of_re_lt_half
      hs him hre
  filter_upwards [hcorrPred, htail, hdom] with K hcorrK htailK hdomK
  have habs :
      |etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s| <
        -etaCriticalMirrorRotatedDefectProjectionTail K s :=
    hcorrK.trans_lt hdomK
  have hupper := lt_of_abs_lt habs
  rw [etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    hs him K]
  linarith

end DkMath.RH.CFBRCProjection
