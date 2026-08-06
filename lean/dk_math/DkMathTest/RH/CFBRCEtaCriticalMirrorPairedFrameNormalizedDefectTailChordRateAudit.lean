/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordRateAudit

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailChordRateAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorTransportDefectEndpoint (2 * (k + 1)) s)
      atTop (nhds 0) :=
  etaCriticalMirrorEvenDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (a : ℝ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedDefectTail a s k =
      -etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k :=
  etaCriticalMirrorIndexNormalizedDefectTail_eq_neg_evenDefectEndpoint
    hs him a k

example {a : ℝ} {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse a s) :
    Tendsto
      (etaCriticalMirrorIndexNormalizedDefectTail a s)
      atTop (nhds 0) :=
  etaCriticalMirrorIndexNormalizedDefectTail_tendsto_zero_of_evenEndpointRateCollapse
    hs him hrate

example {a : ℝ} {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse a s) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse a s :=
  etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_evenEndpointRateCollapse
    hs him hrate

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s) :
    EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s :=
  etaCriticalMirrorZeroLocusTwoScaleChordCollapse_of_dominantEndpointRateCollapse
    hs him hrate

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s) :
    s.re = (1 : ℝ) / 2 :=
  re_eq_half_of_nontrivialRiemannZetaZero_of_dominantEndpointRateCollapse
    hs him hrate

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailChordRateAudit
