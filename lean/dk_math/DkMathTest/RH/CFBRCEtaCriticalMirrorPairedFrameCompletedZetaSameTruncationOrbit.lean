/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSameTruncationOrbit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaSameTruncationOrbit"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example :
    EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility :=
  etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_lineCompatibility

example
    (horbit :
      EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSameTruncationOrbitResidualCollapse
    horbit

#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_conj
#print axioms etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_lineCompatibility
#print axioms riemannHypothesis_of_endpointCompletedZetaSameTruncationOrbitResidualCollapse

end DkMathTest.RH.CFBRCProjection
