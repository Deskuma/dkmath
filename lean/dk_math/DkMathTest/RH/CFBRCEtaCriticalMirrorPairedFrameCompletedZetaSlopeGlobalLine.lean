/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeGlobalLine

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaSlopeGlobalLine"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example :
    EtaCriticalMirrorGlobalZeroLineLock
      completedZetaCanonicalSlopeCarrier :=
  completedZetaCanonicalSlopeGlobalZeroLineLock

example
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    EtaCriticalMirrorGlobalZeroLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier :=
  etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeCompatibility
    hcompat

example
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSlopeCompatibility hcompat

#print axioms completedZetaCanonicalSlopeGlobalZeroLineLock
#print axioms etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeCompatibility
#print axioms riemannHypothesis_of_endpointCompletedZetaSlopeCompatibility

end DkMathTest.RH.CFBRCProjection
