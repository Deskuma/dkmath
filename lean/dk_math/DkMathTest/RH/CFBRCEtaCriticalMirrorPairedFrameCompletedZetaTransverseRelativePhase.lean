/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseRelativePhase

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaTransverseRelativePhase"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (k : ℕ) (s : ℂ) :
    ‖etaCriticalMirrorCompletedZetaRelativeCounterRotation k s‖ = 1 := by
  exact norm_etaCriticalMirrorCompletedZetaRelativeCounterRotation k s

example (k : ℕ) (s : ℂ) :
    etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s =
      (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).re *
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).im +
        (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im *
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).re := by
  exact
    etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase_split
      k s

example
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s)
        atTop (nhds 0) ↔
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im)
        atTop (nhds 0) := by
  exact
    etaCriticalMirrorCompletedZetaDominantTransverse_tendsto_zero_iff_relativePhase_im_tendsto_zero
      hs him hre

example
    (htransverse :
      EtaCriticalMirrorCompletedZetaDominantTransverseCollapse) :
    EtaCriticalMirrorCompletedZetaRelativePhaseImagCollapse := by
  exact
    etaCriticalMirrorCompletedZetaRelativePhaseImagCollapse_of_transverseCollapse
      htransverse

#print axioms etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase_split
#print axioms etaCriticalMirrorCompletedZetaDominantTransverse_tendsto_zero_iff_relativePhase_im_tendsto_zero
#print axioms etaCriticalMirrorCompletedZetaRelativePhaseImagCollapse_of_transverseCollapse

end DkMathTest.RH.CFBRCProjection
