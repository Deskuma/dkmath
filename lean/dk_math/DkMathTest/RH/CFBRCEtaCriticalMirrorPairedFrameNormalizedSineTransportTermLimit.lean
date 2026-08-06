/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example :
    Tendsto etaPairFrameScaledLogStep atTop (nhds 1) :=
  etaPairFrameScaledLogStep_tendsto_one

example (s : ℂ) :
    Tendsto (etaPairFrameScaledStepPhase s) atTop (nhds s.im) :=
  etaPairFrameScaledStepPhase_tendsto_im s

example (s : ℂ) :
    Tendsto
      (etaCriticalMirrorPairedFrameScaledSineTransportCoefficient s)
      atTop (nhds (s.im ^ 2)) :=
  etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_tendsto_sq s

example (z : ℂ) :
    0 < etaPairIndexNormalizedTailConstantReal z :=
  etaPairIndexNormalizedTailConstantReal_pos z

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k).re)
      atTop
      (nhds (etaPairIndexNormalizedTailConstantReal (criticalMirror s))) :=
  etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_re_tendsto_constant
    hs hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ ((criticalMirror s).re + 1)) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k)
      atTop
      (nhds (etaCriticalMirrorRightNormalizedSineTransportTermConstant s)) :=
  etaCriticalMirrorRightNormalizedSineTransportTerm_tendsto_constant
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ (s.re + 1)) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k)
      atTop
      (nhds (etaCriticalMirrorLeftNormalizedSineTransportTermConstant s)) :=
  etaCriticalMirrorLeftNormalizedSineTransportTerm_tendsto_constant
    hs him hre

end DkMath.RH.CFBRCProjection
