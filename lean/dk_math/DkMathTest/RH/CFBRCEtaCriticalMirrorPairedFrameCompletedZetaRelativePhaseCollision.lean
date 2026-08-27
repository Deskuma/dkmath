/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRelativePhaseCollision

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaRelativePhaseCollision"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (k : ℕ) (s : ℂ) :
    etaCriticalMirrorCompletedZetaRelativeCounterRotation k s =
      (completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
        Complex.exp
          (Complex.I * (((etaPairLogarithmicCounterPhase k s : ℝ) : ℂ))) := by
  exact
    etaCriticalMirrorCompletedZetaRelativeCounterRotation_eq_fixed_mul_exp k s

example {s : ℂ} (him : s.im ≠ 0) :
    ¬ Tendsto
      (fun k : ℕ =>
        (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im)
      atTop (nhds 0) := by
  exact
    not_etaCriticalMirrorCompletedZetaRelativeCounterRotation_im_tendsto_zero
      him

example
    (hphase : EtaCriticalMirrorCompletedZetaRelativePhaseImagCollapse) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_completedZetaRelativePhaseImagCollapse hphase

#print axioms etaCriticalMirrorCompletedZetaRelativeCounterRotation_eq_fixed_mul_exp
#print axioms not_etaCriticalMirrorCompletedZetaRelativeCounterRotation_im_tendsto_zero
#print axioms riemannHypothesis_of_completedZetaRelativePhaseImagCollapse

end DkMathTest.RH.CFBRCProjection
