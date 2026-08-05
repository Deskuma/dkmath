/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailPhaseLock

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaTailPhaseLock"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ => etaCriticalMirrorCompletedZetaTailMovingPhase k s)
      atTop (nhds 1) :=
  etaCriticalMirrorCompletedZetaTailMovingPhase_tendsto_one_of_residualCollapse
    htail hs him hre

example
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 :=
  etaCriticalMirror_re_eq_half_of_completedZetaWeightedTailOrbitResidualCollapse
    htail hs him

example
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_completedZetaWeightedTailPhaseLockCollision htail

#print axioms etaCriticalMirrorCompletedZetaTailMovingPhase_tendsto_one_of_residualCollapse
#print axioms etaCriticalMirror_re_eq_half_of_completedZetaWeightedTailOrbitResidualCollapse
#print axioms riemannHypothesis_of_completedZetaWeightedTailPhaseLockCollision

end DkMathTest.RH.CFBRCProjection
