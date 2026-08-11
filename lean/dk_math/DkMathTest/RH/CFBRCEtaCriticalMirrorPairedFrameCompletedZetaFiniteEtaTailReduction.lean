/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaTailReduction

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaTailReduction"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorFinitePairedEtaDefect k s =
      -etaCriticalMirrorDefectPairTail (k + 1) s :=
  etaCriticalMirrorFinitePairedEtaDefect_eq_neg_tail_of_zero hs him k

example :
    EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse :=
  etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse_iff_weightedTailOrbitResidualCollapse

example
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaWeightedTailOrbitResidualCollapse
    htail

#print axioms etaCriticalMirrorFinitePairedEtaDefect_eq_neg_tail_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse_iff_weightedTailOrbitResidualCollapse
#print axioms riemannHypothesis_of_endpointCompletedZetaWeightedTailOrbitResidualCollapse

end DkMathTest.RH.CFBRCProjection
