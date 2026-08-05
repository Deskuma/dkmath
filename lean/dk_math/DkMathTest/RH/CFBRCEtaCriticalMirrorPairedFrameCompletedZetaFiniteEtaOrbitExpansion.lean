/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaOrbitExpansion

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaOrbitExpansion"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k =
      (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
        (DkMath.RH.Weave.Analytic.etaPairedPartial
            (k + 1) (criticalMirror s) -
          DkMath.RH.Weave.Analytic.etaPairedPartial (k + 1) s) :=
  etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_eq_indexPow_mul_etaPairedPartial_sub
    a s k

example :
    EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse :=
  etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_weightedFiniteEtaOrbitResidualCollapse

example
    (hfinite :
      EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse
    hfinite

#print axioms etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_eq_indexPow_mul_etaPairedPartial_sub
#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_finiteEtaCarrier
#print axioms etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_weightedFiniteEtaOrbitResidualCollapse
#print axioms riemannHypothesis_of_endpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse

end DkMathTest.RH.CFBRCProjection
