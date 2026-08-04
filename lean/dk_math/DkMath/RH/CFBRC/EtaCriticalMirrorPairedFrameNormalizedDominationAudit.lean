/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityBlock
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominationAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

namespace EtaPairPositiveDensityBlockSchedule

/-- Limiting right block lower-bound constant at the pair-left endpoint scale. -/
noncomputable def rightNormalizedBlockMarginConstant
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : ℝ :=
  (s.im ^ 2 / 4) *
    (S.density *
      (1 + 2 * S.density) ^ (s.re - 2))

/-- Limiting left block lower-bound constant at the pair-left endpoint scale. -/
noncomputable def leftNormalizedBlockMarginConstant
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : ℝ :=
  (s.im ^ 2 / 4) *
    (S.density *
      (1 + 2 * S.density) ^ (-s.re - 1))

/-- Right constant-level gate for domination of the coarse Abel correction bound. -/
def RightNormalizedAbelCorrectionConstantDominates
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : Prop :=
  etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s <
    S.rightNormalizedBlockMarginConstant s

/-- Left constant-level gate for domination of the coarse Abel correction bound. -/
def LeftNormalizedAbelCorrectionConstantDominates
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : Prop :=
  etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s <
    S.leftNormalizedBlockMarginConstant s

/-- Right block-minus-correction constant gap. -/
noncomputable def rightNormalizedAbelCorrectionDominationGap
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : ℝ :=
  S.rightNormalizedBlockMarginConstant s -
    etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s

/-- Left block-minus-correction constant gap. -/
noncomputable def leftNormalizedAbelCorrectionDominationGap
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : ℝ :=
  S.leftNormalizedBlockMarginConstant s -
    etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s

/-- The right constant gate is exactly positivity of the right constant gap. -/
theorem rightNormalizedAbelCorrectionConstantDominates_iff_gap_pos
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    S.RightNormalizedAbelCorrectionConstantDominates s ↔
      0 < S.rightNormalizedAbelCorrectionDominationGap s := by
  unfold RightNormalizedAbelCorrectionConstantDominates
  unfold rightNormalizedAbelCorrectionDominationGap
  constructor <;> intro h <;> linarith

/-- The left constant gate is exactly positivity of the left constant gap. -/
theorem leftNormalizedAbelCorrectionConstantDominates_iff_gap_pos
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    S.LeftNormalizedAbelCorrectionConstantDominates s ↔
      0 < S.leftNormalizedAbelCorrectionDominationGap s := by
  unfold LeftNormalizedAbelCorrectionConstantDominates
  unfold leftNormalizedAbelCorrectionDominationGap
  constructor <;> intro h <;> linarith

/--
A strict right constant gap eventually places the predecessor correction power
bound below the explicit right block power lower bound.
-/
theorem eventually_correctionPowerBound_lt_rightBlockMarginPowerLowerBound
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
          s (K - 1) <
        etaCriticalMirrorRightBlockMarginPowerLowerBound
          s K (S.blockLength K) := by
  have hcorr :=
    etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrectionPowerBound_tendsto
      hre
  have hblock0 := S.rightNormalizedBlockMarginPowerLowerBound_tendsto s
  have hblock :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorRightBlockMarginPowerLowerBound
              s K (S.blockLength K))
        atTop
        (nhds (S.rightNormalizedBlockMarginConstant s)) := by
    simpa [rightNormalizedBlockMarginConstant, criticalMirror_re] using hblock0
  let midpoint : ℝ :=
    (etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s +
      S.rightNormalizedBlockMarginConstant s) / 2
  have hcorrMid :
      etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s < midpoint := by
    dsimp [midpoint]
    unfold RightNormalizedAbelCorrectionConstantDominates at hdom
    linarith
  have hMidBlock :
      midpoint < S.rightNormalizedBlockMarginConstant s := by
    dsimp [midpoint]
    unfold RightNormalizedAbelCorrectionConstantDominates at hdom
    linarith
  have hcorrEventually :
      ∀ᶠ K : ℕ in atTop,
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
              s (K - 1) <
          midpoint :=
    (tendsto_order.1 hcorr).2 midpoint hcorrMid
  have hblockEventually :
      ∀ᶠ K : ℕ in atTop,
        midpoint <
          etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorRightBlockMarginPowerLowerBound
              s K (S.blockLength K) :=
    (tendsto_order.1 hblock).1 midpoint hMidBlock
  filter_upwards [hcorrEventually, hblockEventually] with K hcorrK hblockK
  have hnormalized :
      etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
            s (K - 1) <
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          etaCriticalMirrorRightBlockMarginPowerLowerBound
            s K (S.blockLength K) :=
    hcorrK.trans hblockK
  have hscale : 0 < etaPairFrameLeftEndpoint K ^ (criticalMirror s).re :=
    Real.rpow_pos_of_pos (etaPairFrameLeftEndpoint_pos K) _
  exact lt_of_mul_lt_mul_left hnormalized hscale.le

/--
A strict left constant gap eventually places the predecessor correction power
bound below the explicit left block power lower bound.
-/
theorem eventually_correctionPowerBound_lt_leftBlockMarginPowerLowerBound
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
          s (K - 1) <
        etaCriticalMirrorLeftBlockMarginPowerLowerBound
          s K (S.blockLength K) := by
  have hcorr :=
    etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrectionPowerBound_tendsto
      hre
  have hblock0 := S.leftNormalizedBlockMarginPowerLowerBound_tendsto s
  have hblock :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorLeftBlockMarginPowerLowerBound
              s K (S.blockLength K))
        atTop
        (nhds (S.leftNormalizedBlockMarginConstant s)) := by
    simpa [leftNormalizedBlockMarginConstant] using hblock0
  let midpoint : ℝ :=
    (etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s +
      S.leftNormalizedBlockMarginConstant s) / 2
  have hcorrMid :
      etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s < midpoint := by
    dsimp [midpoint]
    unfold LeftNormalizedAbelCorrectionConstantDominates at hdom
    linarith
  have hMidBlock :
      midpoint < S.leftNormalizedBlockMarginConstant s := by
    dsimp [midpoint]
    unfold LeftNormalizedAbelCorrectionConstantDominates at hdom
    linarith
  have hcorrEventually :
      ∀ᶠ K : ℕ in atTop,
        etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
              s (K - 1) <
          midpoint :=
    (tendsto_order.1 hcorr).2 midpoint hcorrMid
  have hblockEventually :
      ∀ᶠ K : ℕ in atTop,
        midpoint <
          etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorLeftBlockMarginPowerLowerBound
              s K (S.blockLength K) :=
    (tendsto_order.1 hblock).1 midpoint hMidBlock
  filter_upwards [hcorrEventually, hblockEventually] with K hcorrK hblockK
  have hnormalized :
      etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
            s (K - 1) <
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorLeftBlockMarginPowerLowerBound
            s K (S.blockLength K) :=
    hcorrK.trans hblockK
  have hscale : 0 < etaPairFrameLeftEndpoint K ^ s.re :=
    Real.rpow_pos_of_pos (etaPairFrameLeftEndpoint_pos K) _
  exact lt_of_mul_lt_mul_left hnormalized hscale.le

/-- A strict right constant gap supplies the earlier right Abel domination gate. -/
theorem rightAbelCorrectionTailDominated_of_normalizedConstantDomination
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightNormalizedAbelCorrectionConstantDominates s) :
    RightAbelCorrectionTailDominated s := by
  have hcorrLower :=
    S.eventually_correctionPowerBound_lt_rightBlockMarginPowerLowerBound
      hre hdom
  have hmarginTail :=
    S.eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail
      hs him hre
  filter_upwards [hcorrLower, hmarginTail] with K hcorrK htailK
  have hlower :=
    etaCriticalMirrorRightBlockMarginPowerLowerBound_le
      hs K (S.blockLength K)
  exact (hcorrK.trans_le hlower).trans htailK

/-- A strict left constant gap supplies the earlier left Abel domination gate. -/
theorem leftAbelCorrectionTailDominated_of_normalizedConstantDomination
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftNormalizedAbelCorrectionConstantDominates s) :
    LeftAbelCorrectionTailDominated s := by
  have hcorrLower :=
    S.eventually_correctionPowerBound_lt_leftBlockMarginPowerLowerBound
      hre hdom
  have hmarginTail :=
    S.eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
      hs him hre
  filter_upwards [hcorrLower, hmarginTail] with K hcorrK htailK
  have hlower :=
    etaCriticalMirrorLeftBlockMarginPowerLowerBound_le
      hs K (S.blockLength K)
  exact (hcorrK.trans_le hlower).trans htailK

/-- Right normalized constant domination forces the predecessor whole-tail projection positive. -/
theorem eventually_predecessorFrameWholeTailProjection_pos_of_normalizedConstantDomination
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorPredecessorFrameWholeTailProjection K s :=
  eventually_predecessorFrameWholeTailProjection_pos_of_rightAbelCorrectionTailDominated
    hs him hre
    (S.rightAbelCorrectionTailDominated_of_normalizedConstantDomination
      hs him hre hdom)

/-- Left normalized constant domination forces the predecessor whole-tail projection negative. -/
theorem eventually_predecessorFrameWholeTailProjection_neg_of_normalizedConstantDomination
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPredecessorFrameWholeTailProjection K s < 0 :=
  eventually_predecessorFrameWholeTailProjection_neg_of_leftAbelCorrectionTailDominated
    hs him hre
    (S.leftAbelCorrectionTailDominated_of_normalizedConstantDomination
      hs him hre hdom)

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
