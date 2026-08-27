/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseBridge

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaTransverseBridge"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    completedZetaCanonicalSlopeCarrier k s =
      (completedZetaCanonicalDisplacement k)⁻¹ *
        completedRiemannZeta
          (s + completedZetaCanonicalDisplacement k) := by
  exact
    completedZetaCanonicalSlopeCarrier_eq_normalizedNearbyValue_of_zero hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s =
      complexRealLineDefect
        (completedZetaCanonicalSlopeDirection s)
        (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
          (completedZetaCanonicalDisplacement k)⁻¹ *
            completedRiemannZeta
              (s + completedZetaCanonicalDisplacement k)) := by
  exact
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_nearbyValueDefect_of_zero
      hs k

example :
    EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility := by
  exact
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_iff_lineCompatibility

example
    (hbridge :
      EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_endpointCompletedZetaSlopeTransverseBridgeCollapse
      hbridge

#print axioms completedZetaCanonicalSlopeCarrier_eq_normalizedNearbyValue_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_nearbyValueDefect_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_iff_lineCompatibility
#print axioms riemannHypothesis_of_endpointCompletedZetaSlopeTransverseBridgeCollapse

end DkMathTest.RH.CFBRCProjection
