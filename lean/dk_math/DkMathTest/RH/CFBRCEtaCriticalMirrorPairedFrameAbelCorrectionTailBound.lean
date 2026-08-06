/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelCorrectionTailBound

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameAbelCorrectionTailBound"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameAbelCorrectionTailBound

open Filter
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : 0 < s.re)
    (hm : 0 < (criticalMirror s).re)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑' n : ℕ,
      etaCriticalMirrorPairedFrameCorrectionMajorant s (n + K)) ≤
      etaCriticalMirrorPairedFrameCorrectionTailPowerBound s K :=
  tsum_etaCriticalMirrorPairedFrameCorrectionMajorant_nat_add_le_powerBound
    hs hm hK

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      ‖etaCriticalMirrorPairedFrameCorrectionTail K s‖ ≤
        etaCriticalMirrorPairedFrameCorrectionTailPowerBound s K :=
  eventually_norm_etaCriticalMirrorPairedFrameCorrectionTail_le_powerBound
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      |etaCriticalMirrorPairedFrameCorrectionProjectionTail K s| ≤
        etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K :=
  eventually_abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le_powerBound
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : RightAbelCorrectionTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorPredecessorFrameWholeTailProjection K s :=
  eventually_predecessorFrameWholeTailProjection_pos_of_rightAbelCorrectionTailDominated
    hs him hre hdom

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : LeftAbelCorrectionTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPredecessorFrameWholeTailProjection K s < 0 :=
  eventually_predecessorFrameWholeTailProjection_neg_of_leftAbelCorrectionTailDominated
    hs him hre hdom

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameAbelCorrectionTailBound
