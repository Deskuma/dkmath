/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTailLimit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedSineTransportTailLimit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s)
      atTop
      (nhds (etaCriticalMirrorRightNormalizedSineTransportTailConstant s)) :=
  etaCriticalMirrorRightNormalizedSineTransportTail_tendsto_constant
    hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s)
      atTop
      (nhds (etaCriticalMirrorLeftNormalizedSineTransportTailConstant s)) :=
  etaCriticalMirrorLeftNormalizedSineTransportTail_tendsto_constant
    hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorRightNormalizedSineTransportTailConstant s < 0 :=
  etaCriticalMirrorRightNormalizedSineTransportTailConstant_neg hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorLeftNormalizedSineTransportTailConstant s :=
  etaCriticalMirrorLeftNormalizedSineTransportTailConstant_pos hs him

end DkMath.RH.CFBRCProjection
