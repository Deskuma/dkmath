/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingProjectionTailMargin

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingProjectionTailMargin"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingProjectionTailMargin

open Filter
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (K N : ℕ) :
    etaCriticalMirrorRotatedDefectProjectionTail K s =
      (Finset.range N).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) +
        etaCriticalMirrorRotatedDefectProjectionTail (K + N) s :=
  etaCriticalMirrorRotatedDefectProjectionTail_eq_block_add_tail
    hs K N

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRightBlockMarginSum
          s K (S.blockLength K) <
        etaCriticalMirrorRotatedDefectProjectionTail K s :=
  S.eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail
    hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorLeftBlockMarginSum
          s K (S.blockLength K) <
        -etaCriticalMirrorRotatedDefectProjectionTail K s :=
  S.eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
    hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightBlockMarginDominatesAbelCorrection s) :
    RightAbelCorrectionTailDominated s :=
  S.rightAbelCorrectionTailDominated_of_blockMargin
    hs him hre hdom

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftBlockMarginDominatesAbelCorrection s) :
    LeftAbelCorrectionTailDominated s :=
  S.leftAbelCorrectionTailDominated_of_blockMargin
    hs him hre hdom

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingProjectionTailMargin
