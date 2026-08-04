/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCosineLossAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCosineLossAudit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K)
      atTop (nhds 0) :=
  etaCriticalMirrorRightIndexNormalizedCosineLossPowerBound_tendsto_zero hre

example
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K)
      atTop (nhds 0) :=
  etaCriticalMirrorLeftIndexNormalizedCosineLossPowerBound_tendsto_zero hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
      atTop (nhds 0) :=
  etaCriticalMirrorRightIndexNormalizedCosineLossTail_tendsto_zero
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
      atTop (nhds 0) :=
  etaCriticalMirrorLeftIndexNormalizedCosineLossTail_tendsto_zero
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail (K - 1) s)
      atTop (nhds 0) :=
  etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCosineLossTail_tendsto_zero
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail (K - 1) s)
      atTop (nhds 0) :=
  etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCosineLossTail_tendsto_zero
    hs him hre

end DkMath.RH.CFBRCProjection
