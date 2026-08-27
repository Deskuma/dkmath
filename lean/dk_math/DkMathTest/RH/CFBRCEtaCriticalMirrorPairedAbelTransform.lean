/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelTransform"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelTransform

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (K : ℕ) (s : ℂ) :
    etaCriticalMirrorRotatedDefectPairedPartial K s =
      etaCriticalMirrorPairedAbelBoundaryTerm K s -
        (Finset.range (K - 1)).sum
          (etaCriticalMirrorPairedFrameCorrectionTerm s) :=
  etaCriticalMirrorRotatedDefectPairedPartial_eq_abel K s

example (K : ℕ) (s : ℂ) :
    ‖etaCriticalMirrorPairedAbelBoundaryTerm K s‖ =
      ‖etaCriticalMirrorDefectPairedPartial K s‖ :=
  norm_etaCriticalMirrorPairedAbelBoundaryTerm K s

example (s : ℂ) (k : ℕ)
    (hspan : etaPairFrameStepSpan s k ≤ 1) :
    ‖etaPairBaseRotation s (k + 1) - etaPairBaseRotation s k‖ ≤
      2 * etaPairFrameStepSpan s k :=
  norm_etaPairBaseRotation_succ_sub_le_two_mul_stepSpan s k hspan

example (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      ‖etaPairBaseRotation s (k + 1) - etaPairBaseRotation s k‖ ≤
        2 * etaPairFrameStepSpan s k :=
  eventually_norm_etaPairBaseRotation_succ_sub_le_two_mul_stepSpan s

example (s : ℂ) (k : ℕ)
    (hspan : etaPairFrameStepSpan s k ≤ 1) :
    ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
      2 * etaPairFrameStepSpan s k *
        ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ :=
  norm_etaCriticalMirrorPairedFrameCorrectionTerm_le s k hspan

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelTransform
