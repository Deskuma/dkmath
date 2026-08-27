/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialTransverseDecomposition

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaRadialTransverseDecomposition"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s z : ℂ) :
    z = completedZetaCanonicalSlopeRealProjection s z +
      completedZetaCanonicalSlopeUnitDirection s *
        (Complex.I *
          ((completedZetaCanonicalSlopeTransverseCoordinate s z : ℝ) : ℂ)) := by
  exact completedZetaCanonicalSlope_eq_projection_add_transverse s z

example (s z : ℂ) :
    ‖z - completedZetaCanonicalSlopeRealProjection s z‖ =
      |completedZetaCanonicalSlopeTransverseCoordinate s z| := by
  exact norm_sub_completedZetaCanonicalSlopeRealProjection s z

example (s : ℂ) :
    Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            etaCriticalMirrorCompletedZetaDominantRadialRayModel k s)
        atTop (nhds 0) ↔
      Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s)
          atTop (nhds 0) ∧
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s)
          atTop (nhds 0) := by
  exact etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff s

example :
    EtaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation ↔
      EtaCriticalMirrorCompletedZetaDominantRadialCoordinateCollapse ∧
        EtaCriticalMirrorCompletedZetaDominantTransverseCollapse := by
  exact
    etaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation_iff_coordinates

#print axioms completedZetaCanonicalSlope_eq_projection_add_transverse
#print axioms norm_sub_completedZetaCanonicalSlopeRealProjection
#print axioms etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff
#print axioms etaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation_iff_coordinates

end DkMathTest.RH.CFBRCProjection
