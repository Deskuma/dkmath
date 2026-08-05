/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelBalanceAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelClosureDecision"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/--
Certificate that a normalized Abel balance closes by genuine cancellation:
both component constants are nonzero, while their total is exactly zero.
-/
structure EtaCriticalMirrorNormalizedAbelCancellationCertificate
    (moving correction : ℝ) : Prop where
  moving_ne_zero : moving ≠ 0
  correction_ne_zero : correction ≠ 0
  total_eq_zero : moving + correction = 0

/-- Residual left by the right normalized Abel closure attempt. -/
noncomputable def etaCriticalMirrorRightNormalizedAbelClosureResidual
    (s : ℂ) : ℝ :=
  etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s +
    etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s

/-- Residual left by the left normalized Abel closure attempt. -/
noncomputable def etaCriticalMirrorLeftNormalizedAbelClosureResidual
    (s : ℂ) : ℝ :=
  etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s +
    etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s

/-- The right normalized Abel closure residual is identically zero. -/
theorem etaCriticalMirrorRightNormalizedAbelClosureResidual_eq_zero
    (s : ℂ) :
    etaCriticalMirrorRightNormalizedAbelClosureResidual s = 0 := by
  unfold etaCriticalMirrorRightNormalizedAbelClosureResidual
  unfold etaCriticalMirrorRightNormalizedMovingProjectionTailConstant
  ring

/-- The left normalized Abel closure residual is identically zero. -/
theorem etaCriticalMirrorLeftNormalizedAbelClosureResidual_eq_zero
    (s : ℂ) :
    etaCriticalMirrorLeftNormalizedAbelClosureResidual s = 0 := by
  unfold etaCriticalMirrorLeftNormalizedAbelClosureResidual
  unfold etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant
  ring

/--
At a nonreal nontrivial zero, the right normalized Abel components form a
nonzero cancellation certificate rather than a zero/nonzero collision.
-/
theorem etaCriticalMirrorRightNormalizedAbelCancellationCertificate
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorNormalizedAbelCancellationCertificate
      (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)
      (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s) := by
  rcases
      etaCriticalMirrorRightNormalizedAbelBalance_nonzero_cancellation hs him with
    ⟨hmove, hcorr, htotal⟩
  exact ⟨hmove.ne', hcorr.ne, htotal⟩

/--
At a nonreal nontrivial zero, the left normalized Abel components form a
nonzero cancellation certificate rather than a zero/nonzero collision.
-/
theorem etaCriticalMirrorLeftNormalizedAbelCancellationCertificate
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorNormalizedAbelCancellationCertificate
      (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)
      (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s) := by
  rcases
      etaCriticalMirrorLeftNormalizedAbelBalance_nonzero_cancellation hs him with
    ⟨hmove, hcorr, htotal⟩
  exact ⟨hmove.ne, hcorr.ne', htotal⟩

/--
Right-side Gate 5 decision: the present normalized Abel route has zero residual
because two nonzero constants cancel exactly.
-/
theorem etaCriticalMirrorRightNormalizedAbelClosureDecision
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorRightNormalizedAbelClosureResidual s = 0 ∧
      EtaCriticalMirrorNormalizedAbelCancellationCertificate
        (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)
        (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s) := by
  exact
    ⟨etaCriticalMirrorRightNormalizedAbelClosureResidual_eq_zero s,
      etaCriticalMirrorRightNormalizedAbelCancellationCertificate hs him⟩

/--
Left-side Gate 5 decision: the present normalized Abel route has zero residual
because two nonzero constants cancel exactly.
-/
theorem etaCriticalMirrorLeftNormalizedAbelClosureDecision
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorLeftNormalizedAbelClosureResidual s = 0 ∧
      EtaCriticalMirrorNormalizedAbelCancellationCertificate
        (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)
        (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s) := by
  exact
    ⟨etaCriticalMirrorLeftNormalizedAbelClosureResidual_eq_zero s,
      etaCriticalMirrorLeftNormalizedAbelCancellationCertificate hs him⟩

end DkMath.RH.CFBRCProjection
