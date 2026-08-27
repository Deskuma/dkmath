/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeCompatibilityAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaSlopeCompatibilityAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantNormalizedEndpointCarrier k s)
      atTop (nhds (deriv completedRiemannZeta s)) :=
  etaCriticalMirrorDominantNormalizedEndpointCarrier_tendsto_deriv_of_completedZetaSlopeCompatibility
    hcompat hs him

example
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    deriv completedRiemannZeta s ≠ 0 :=
  deriv_completedRiemannZeta_ne_zero_of_completedZetaSlopeCompatibility_of_offCritical
    hcompat hs him hre

example
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility :=
  etaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility_of_valueCompatibility
    hcompat

example
    (hline : EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility) :
    EtaCriticalMirrorGlobalZeroLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier :=
  etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeLineCompatibility
    hline

example
    (hline : EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSlopeLineCompatibility hline

#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_tendsto_deriv_of_completedZetaSlopeCompatibility
#print axioms deriv_completedRiemannZeta_ne_zero_of_completedZetaSlopeCompatibility_of_offCritical
#print axioms riemannHypothesis_of_endpointCompletedZetaSlopeLineCompatibility

end DkMathTest.RH.CFBRCProjection
