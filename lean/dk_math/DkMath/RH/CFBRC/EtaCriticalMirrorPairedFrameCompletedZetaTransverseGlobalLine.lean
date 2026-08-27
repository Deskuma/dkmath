/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialTransverseDecomposition
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionContracts

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseGlobalLine"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- The transverse coordinate is the defect from the unit completed-zeta line. -/
theorem complexRealLineDefect_completedZetaCanonicalSlopeUnitDirection_eq_transverseCoordinate
    (s z : ℂ) :
    complexRealLineDefect
        (completedZetaCanonicalSlopeUnitDirection s) z =
      completedZetaCanonicalSlopeTransverseCoordinate s z := by
  rfl

/-- Transverse collapse supplies a fixed global line lock for the endpoint. -/
def etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaTransverseCollapse
    (htransverse :
      EtaCriticalMirrorCompletedZetaDominantTransverseCollapse) :
    EtaCriticalMirrorGlobalZeroLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier where
  globalDirection := completedZetaCanonicalSlopeUnitDirection
  globalDirection_ne_zero := by
    intro s _hs _him
    exact completedZetaCanonicalSlopeUnitDirection_ne_zero s
  carrier_tendsto_global_line := by
    intro s hs him
    have h := htransverse hs him
    simpa only [
      etaCriticalMirrorCompletedZetaDominantTransverseCoordinate,
      complexRealLineDefect_completedZetaCanonicalSlopeUnitDirection_eq_transverseCoordinate]
      using h

/-- Full radial-ray approximation implies the weaker transverse collapse. -/
theorem etaCriticalMirrorCompletedZetaDominantTransverseCollapse_of_radialRayModelApproximation
    (happrox :
      EtaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation) :
    EtaCriticalMirrorCompletedZetaDominantTransverseCollapse :=
  (etaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation_iff_coordinates.mp
    happrox).2

#print axioms complexRealLineDefect_completedZetaCanonicalSlopeUnitDirection_eq_transverseCoordinate
#print axioms etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaTransverseCollapse

end DkMath.RH.CFBRCProjection
