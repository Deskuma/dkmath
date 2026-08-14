/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit

/-!
# CS8: prime-side arithmetic upper-envelope audit

This module starts after the CS6--CS7 smoothing layer.  It records the
one-sided consequences of the already proved finite-radius approximation
bound and the eventual small-box condition, but does not turn those facts
into an arithmetic sign theorem.  The independent upper envelope remains a
separate source question.

In particular, the fixed centered-Xi defect, horizontal zero energy,
anti-mirror energy, RH-equivalent vanishing statements, and limit exchange
are not used as an arithmetic upper-bound provider here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## CS7 convenience wrappers -/

/-- The CS7 absolute smoothing estimate gives the lower one-sided comparison.
This is an approximation wrapper, not a sign-producing arithmetic theorem. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_ge_fixedDefect_sub_smoothingEnvelope
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsmall : ε * W.R ≤ 1) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R -
        pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope ε W.R ≤
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W := by
  have h :=
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_sub_fixedDefect_abs_le_smoothingEnvelope
      hε W hsmall
  rcases abs_le.mp h with ⟨hneg, _⟩
  linarith

/-- The CS7 absolute smoothing estimate gives the upper one-sided comparison.
This is the side needed by a future independent arithmetic envelope, but is
not itself such an envelope. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_le_fixedDefect_add_smoothingEnvelope
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsmall : ε * W.R ≤ 1) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R +
        pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope ε W.R := by
  have h :=
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_sub_fixedDefect_abs_le_smoothingEnvelope
      hε W hsmall
  rcases abs_le.mp h with ⟨_, hpos⟩
  linarith

/-- For a fixed finite transport window, the CS7 small-box condition is
eventually true along the prescribed one-sided `ε → 0+` filter. -/
theorem eventually_pascalCenteredXiPrimeSideQuadraticization_smallBox
    (W : PascalCenteredXiResidueTransportWindow) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * W.R ≤ 1 := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (nhds 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hconst : Tendsto (fun _ : ℝ => W.R) (𝓝[>] 0) (nhds W.R) :=
    tendsto_const_nhds
  have hmul : Tendsto (fun ε : ℝ => ε * W.R) (𝓝[>] 0) (nhds 0) :=
    by simpa using hid.mul hconst
  exact hmul.eventually (eventually_le_nhds (by norm_num))

/-! ## CS8 source audit -/

/-- The current finite prime-side ledger is exposed for the CS8 audit.  It is
still a one-index linear source ledger; this theorem does not manufacture a
quadratic ordering or a vanishing upper envelope. -/
theorem pascalCenteredXiPrimeSideArithmeticUpperEnvelope_source_ledger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinFiniteArithmeticApproximant ε 0 W X =
      2 * pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum ε W X +
      2 * pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow :=
  pascalCenteredXiPrimeSideQuadraticization_source_ledger hε W X

/-- Green-B closeout for the current audit: no independent arithmetic
vanishing upper envelope has yet been derived from the prime-side source.
This is a named frontier, not an impossibility theorem. -/
inductive PascalCenteredXiPrimeSideArithmeticUpperEnvelopeGap : Prop
  | noIndependentVanishingArithmeticUpperEnvelope :
      PascalCenteredXiPrimeSideArithmeticUpperEnvelopeGap

end DkMath.RH.CFBRCProjection
