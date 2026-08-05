/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominationAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDominationAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDominationAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

namespace EtaPairPositiveDensityBlockSchedule

example
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    S.RightNormalizedAbelCorrectionConstantDominates s ↔
      0 < S.rightNormalizedAbelCorrectionDominationGap s :=
  S.rightNormalizedAbelCorrectionConstantDominates_iff_gap_pos s

example
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    S.LeftNormalizedAbelCorrectionConstantDominates s ↔
      0 < S.leftNormalizedAbelCorrectionDominationGap s :=
  S.leftNormalizedAbelCorrectionConstantDominates_iff_gap_pos s

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
          s (K - 1) <
        etaCriticalMirrorRightBlockMarginPowerLowerBound
          s K (S.blockLength K) :=
  S.eventually_correctionPowerBound_lt_rightBlockMarginPowerLowerBound
    hre hdom

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
          s (K - 1) <
        etaCriticalMirrorLeftBlockMarginPowerLowerBound
          s K (S.blockLength K) :=
  S.eventually_correctionPowerBound_lt_leftBlockMarginPowerLowerBound
    hre hdom

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightNormalizedAbelCorrectionConstantDominates s) :
    RightAbelCorrectionTailDominated s :=
  S.rightAbelCorrectionTailDominated_of_normalizedConstantDomination
    hs him hre hdom

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftNormalizedAbelCorrectionConstantDominates s) :
    LeftAbelCorrectionTailDominated s :=
  S.leftAbelCorrectionTailDominated_of_normalizedConstantDomination
    hs him hre hdom

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorPredecessorFrameWholeTailProjection K s :=
  S.eventually_predecessorFrameWholeTailProjection_pos_of_normalizedConstantDomination
    hs him hre hdom

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftNormalizedAbelCorrectionConstantDominates s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPredecessorFrameWholeTailProjection K s < 0 :=
  S.eventually_predecessorFrameWholeTailProjection_neg_of_normalizedConstantDomination
    hs him hre hdom

end EtaPairPositiveDensityBlockSchedule

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDominationAudit
