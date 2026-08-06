/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionProjectionTailLimit

set_option linter.style.longLine false

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionProjectionTailLimit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop
      (nhds
        (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s)) :=
  etaCriticalMirrorRightNormalizedCorrectionProjectionTail_tendsto_constant
    hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop
      (nhds
        (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s)) :=
  etaCriticalMirrorLeftNormalizedCorrectionProjectionTail_tendsto_constant
    hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s < 0 :=
  etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant_neg hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s :=
  etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant_pos hs him

end DkMath.RH.CFBRCProjection
