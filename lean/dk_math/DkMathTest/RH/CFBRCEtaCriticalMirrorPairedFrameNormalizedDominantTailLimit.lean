/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDominantTailLimit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

example (_z : ℂ) :
    Tendsto etaPairIndexToSuccessorEndpointRatio atTop
      (nhds ((1 : ℝ) / 2)) :=
  etaPairIndexToSuccessorEndpointRatio_tendsto_half

example (z : ℂ) :
    Tendsto (etaPairFrameStepPhase z) atTop (nhds 0) :=
  etaPairFrameStepPhase_tendsto_zero z

example (z : ℂ) :
    Tendsto
      (fun k : ℕ =>
        etaPairResidualRotation z k
          (etaPairFrameLeftEndpoint (k + 1)))
      atTop (nhds 1) :=
  etaPairResidualRotation_nextLeft_tendsto_one z

example (z : ℂ) :
    Tendsto
      (etaPairIndexNormalizedRotatedEulerHalfMain z)
      atTop (nhds (etaPairIndexNormalizedTailConstant z)) :=
  etaPairIndexNormalizedRotatedEulerHalfMain_tendsto_constant z

example {z : ℂ} (hzre : 0 < z.re) :
    Tendsto
      (etaPairIndexNormalizedRotatedEulerRemainder z)
      atTop (nhds 0) :=
  etaPairIndexNormalizedRotatedEulerRemainder_tendsto_zero hzre

example {z : ℂ} (hzre : 0 < z.re) :
    Tendsto
      (etaPairIndexNormalizedRotatedTail z)
      atTop (nhds (etaPairIndexNormalizedTailConstant z)) :=
  etaPairIndexNormalizedRotatedTail_tendsto_constant hzre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re : ℝ) : ℂ) *
          etaCriticalMirrorPairFrameRotatedDefectTail s k)
      atTop
      (nhds (etaPairIndexNormalizedTailConstant (criticalMirror s))) :=
  etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant hs hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ s.re : ℝ) : ℂ) *
          etaCriticalMirrorPairFrameRotatedDefectTail s k)
      atTop
      (nhds (-etaPairIndexNormalizedTailConstant s)) :=
  etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant hs hre

end DkMath.RH.CFBRCProjection
