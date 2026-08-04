/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTailLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportReduction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionProjectionTailLimit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Right-side normalized correction-projection tail constant. -/
noncomputable def etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant
    (s : ℂ) : ℝ :=
  etaCriticalMirrorRightNormalizedSineTransportTailConstant s

/-- Left-side normalized correction-projection tail constant. -/
noncomputable def etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant
    (s : ℂ) : ℝ :=
  etaCriticalMirrorLeftNormalizedSineTransportTailConstant s

/--
Right of the critical line, the normalized full correction projection has the
same explicit negative limit as its sine-transport main term.
-/
theorem etaCriticalMirrorRightNormalizedCorrectionProjectionTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop
      (nhds
        (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s)) := by
  have hsine :=
    etaCriticalMirrorRightNormalizedSineTransportTail_tendsto_constant
      hs him hre
  have hcos :=
    etaCriticalMirrorRightIndexNormalizedCosineLossTail_tendsto_zero
      hs him hre
  have hsum := hsine.add hcos
  have hlimit :
      Tendsto
        (fun K : ℕ =>
          ((K : ℝ) ^ (criticalMirror s).re) *
              etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s +
            ((K : ℝ) ^ (criticalMirror s).re) *
              etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
        atTop
        (nhds
          (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s)) := by
    simpa [etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant]
      using hsum
  refine hlimit.congr' (Eventually.of_forall fun K => ?_)
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_sineTransportTail_add_cosineLossTail
    hs him K]
  ring

/--
Left of the critical line, the normalized full correction projection has the
same explicit positive limit as its sine-transport main term.
-/
theorem etaCriticalMirrorLeftNormalizedCorrectionProjectionTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s)
      atTop
      (nhds
        (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s)) := by
  have hsine :=
    etaCriticalMirrorLeftNormalizedSineTransportTail_tendsto_constant
      hs him hre
  have hcos :=
    etaCriticalMirrorLeftIndexNormalizedCosineLossTail_tendsto_zero
      hs him hre
  have hsum := hsine.add hcos
  have hlimit :
      Tendsto
        (fun K : ℕ =>
          ((K : ℝ) ^ s.re) *
              etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s +
            ((K : ℝ) ^ s.re) *
              etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
        atTop
        (nhds
          (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s)) := by
    simpa [etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant]
      using hsum
  refine hlimit.congr' (Eventually.of_forall fun K => ?_)
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_sineTransportTail_add_cosineLossTail
    hs him K]
  ring

/-- The right normalized correction-projection tail constant is strictly negative. -/
theorem etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant_neg
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s < 0 := by
  unfold etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant
  exact etaCriticalMirrorRightNormalizedSineTransportTailConstant_neg hs him

/-- The left normalized correction-projection tail constant is strictly positive. -/
theorem etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s := by
  unfold etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant
  exact etaCriticalMirrorLeftNormalizedSineTransportTailConstant_pos hs him

end DkMath.RH.CFBRCProjection
