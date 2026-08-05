/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelTailIdentity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSignedCorrectionDecomposition"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Adjacent pair-frame multiplier after removing the preceding unit frame. -/
noncomputable def etaPairFrameStepMultiplier
    (s : ℂ) (k : ℕ) : ℂ :=
  Complex.exp
      (Complex.I *
        ((etaPairFrameStepPhase s k : ℝ) : ℂ)) -
    1

/-- The partial mirror defect transported into the `k`-th pair-left frame. -/
noncomputable def etaCriticalMirrorPairFrameTransportedDefectPartial
    (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k *
    etaCriticalMirrorDefectPairedPartial (k + 1) s

/-- The real part of the adjacent frame multiplier is the cosine loss. -/
theorem etaPairFrameStepMultiplier_re
    (s : ℂ) (k : ℕ) :
    (etaPairFrameStepMultiplier s k).re =
      Real.cos (etaPairFrameStepPhase s k) - 1 := by
  unfold etaPairFrameStepMultiplier
  simp [Complex.exp_re]

/-- The imaginary part of the adjacent frame multiplier is the sine transport. -/
theorem etaPairFrameStepMultiplier_im
    (s : ℂ) (k : ℕ) :
    (etaPairFrameStepMultiplier s k).im =
      Real.sin (etaPairFrameStepPhase s k) := by
  unfold etaPairFrameStepMultiplier
  simp [Complex.exp_im]

/--
Exact multiplicative factorization of one frame-motion Abel correction.
No norm or triangle inequality is used.
-/
theorem etaCriticalMirrorPairedFrameCorrectionTerm_eq_stepMultiplier_mul
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionTerm s k =
      etaPairFrameStepMultiplier s k *
        etaCriticalMirrorPairFrameTransportedDefectPartial s k := by
  unfold etaCriticalMirrorPairedFrameCorrectionTerm
  unfold etaPairFrameStepMultiplier
  unfold etaCriticalMirrorPairFrameTransportedDefectPartial
  rw [etaPairBaseRotation_succ]
  ring

/-- Signed projection of one exact Abel frame correction. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
    (s : ℂ) (k : ℕ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorPairedFrameCorrectionTerm s k)

/--
First-order sine transport in the signed correction projection.
It couples the adjacent frame angle to the real part of the transported defect partial.
-/
noncomputable def etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
    (s : ℂ) (k : ℕ) : ℝ :=
  s.im * Real.sin (etaPairFrameStepPhase s k) *
    (etaCriticalMirrorPairFrameTransportedDefectPartial s k).re

/--
Cosine-loss part of the signed correction projection.
Its angular coefficient has no linear term at zero.
-/
noncomputable def etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
    (s : ℂ) (k : ℕ) : ℝ :=
  s.im * (Real.cos (etaPairFrameStepPhase s k) - 1) *
    (etaCriticalMirrorPairFrameTransportedDefectPartial s k).im

/--
The signed projection of one Abel frame correction splits exactly into a
sine-transport term and a cosine-loss term.
-/
theorem etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq_sine_add_cosineLoss
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm s k =
      etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k +
        etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s k := by
  unfold etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
  unfold etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
  unfold etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [etaCriticalMirrorPairedFrameCorrectionTerm_eq_stepMultiplier_mul]
  rw [Complex.mul_im]
  rw [etaPairFrameStepMultiplier_re, etaPairFrameStepMultiplier_im]
  ring

/-- Finite signed correction sums inherit the exact sine/cosine split. -/
theorem sum_etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq
    (s : ℂ) (N : ℕ) :
    (Finset.range N).sum
        (etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm s) =
      (Finset.range N).sum
          (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s) +
        (Finset.range N).sum
          (etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s) := by
  simp_rw [etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq_sine_add_cosineLoss]
  exact Finset.sum_add_distrib

/--
The signed projection of the correction tail is the scalar projection of the
termwise correction series.  This keeps all cancellation before any absolute
value is introduced.
-/
theorem etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_tsum_signedTerms
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s =
      ∑' n : ℕ,
        etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
          s (n + K) := by
  have hsum :=
    summable_etaCriticalMirrorPairedFrameCorrectionTail hs him K
  have himag :
      HasSum
        (fun n : ℕ =>
          (etaCriticalMirrorPairedFrameCorrectionTerm s (n + K)).im)
        ((etaCriticalMirrorPairedFrameCorrectionTail K s).im) := by
    unfold etaCriticalMirrorPairedFrameCorrectionTail
    simpa [Function.comp_apply, Function.comp_def] using
      hsum.hasSum.map Complex.imCLM Complex.imCLM.continuous
  have hscaled := himag.mul_left s.im
  unfold etaCriticalMirrorPairedFrameCorrectionProjectionTail
  unfold etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
  unfold etaCriticalMirrorSignedVerticalProjection
  exact hscaled.tsum_eq.symm

/--
Exact signed tail decomposition into the first-order sine transport and the
higher-order cosine loss.  This is the replacement entry point for the failed
absolute-norm correction majorant.
-/
theorem etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_tsum_sine_add_cosineLoss
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s =
      ∑' n : ℕ,
        (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
            s (n + K) +
          etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
            s (n + K)) := by
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_tsum_signedTerms
    hs him K]
  apply tsum_congr
  intro n
  exact
    etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq_sine_add_cosineLoss
      s (n + K)

end DkMath.RH.CFBRCProjection
