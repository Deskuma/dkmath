/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyTransverseBridge

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaTailNearbyTransverseBridge"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorDominantNormalizedEndpointCarrier k s =
      etaCriticalMirrorDominantWeightedTailCarrier k s := by
  exact
    etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_weightedTailCarrier_of_zero
      hs him k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s =
      etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError k s := by
  exact
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_tailNearbyError_of_zero
      hs him k

example :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse := by
  exact
    etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_endpointSlopeBridgeCollapse

example
    (htail :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_weightedTailCompletedZetaNearbyTransverseBridgeCollapse
      htail

#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_weightedTailCarrier_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_tailNearbyError_of_zero
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_endpointSlopeBridgeCollapse
#print axioms riemannHypothesis_of_weightedTailCompletedZetaNearbyTransverseBridgeCollapse

end DkMathTest.RH.CFBRCProjection
