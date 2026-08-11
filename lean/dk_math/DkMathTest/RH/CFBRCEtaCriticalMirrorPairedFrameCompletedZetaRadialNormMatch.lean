/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialNormMatch

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaRadialNormMatch"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (z : ℂ) :
    ‖etaPairIndexNormalizedTailConstant z‖ =
      etaPairIndexNormalizedTailRadius z := by
  exact norm_etaPairIndexNormalizedTailConstant_eq_radius z

example
    {s : ℂ} (hleft : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorCompletedZetaDominantRadialRayModel k s‖)
      atTop (nhds ‖etaPairIndexNormalizedTailConstant s‖) := by
  exact
    norm_etaCriticalMirrorCompletedZetaDominantRadialRayModel_tendsto_left
      hleft

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖ -
          ‖etaCriticalMirrorCompletedZetaDominantRadialRayModel k s‖)
      atTop (nhds 0) := by
  exact
    etaCriticalMirrorDominantEndpoint_sub_rayModel_norm_tendsto_zero_of_offCriticalZero
      hs him hre

#print axioms norm_etaPairIndexNormalizedTailConstant_eq_radius
#print axioms norm_etaCriticalMirrorCompletedZetaDominantRadialRayModel_tendsto_left
#print axioms etaCriticalMirrorDominantEndpoint_sub_rayModel_norm_tendsto_zero_of_offCriticalZero

end DkMathTest.RH.CFBRCProjection
