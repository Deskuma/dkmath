/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit

/-!
# CS9: strength audit for a vanishing upper-envelope contract

This module classifies the logical strength of an arbitrary vanishing
upper-envelope contract at one fixed residue-transport window.  The forward
direction uses the existing ordered-limit adapter.  The converse uses only
the CS7 smoothing comparison and its canonical envelope.

The resulting equivalences are audits of target strength.  They are not an
independent prime-side provider, do not prove a fixed-`ε` sign, and do not
promote a family of transport windows to a global RH statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## CS9-A: fixed-window envelope contract -/

/-- A fixed-window vanishing upper-envelope contract.  This is an audit
surface, not an independent arithmetic provider. -/
def PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ r : ℝ → ℝ,
    Tendsto r (𝓝[>] 0) (nhds 0) ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ r ε

/-- A vanishing upper envelope forces the fixed defect to be nonpositive via
the existing ordered-limit adapter. -/
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_imp_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W →
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  rintro ⟨r, hr, hupper⟩
  exact pascalCenteredXiFixedDefect_nonpos_of_endpoint_le_vanishingEnvelope
    W r hr hupper

/-! ## CS9-B: canonical converse from CS7 -/

/-- If the fixed defect is already nonpositive, the CS7 smoothing envelope is
a canonical vanishing upper envelope.  This is approximation algebra only;
it does not prove the hypothesis. -/
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_of_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow)
    (hD : pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W := by
  refine ⟨
    (fun ε : ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope ε W.R),
    tendsto_pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope_zero
      W.R,
    ?_⟩
  have hsmall := eventually_pascalCenteredXiPrimeSideQuadraticization_smallBox W
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := by
    exact self_mem_nhdsWithin
  filter_upwards [hsmall, hpositive] with ε hsmall hε
  exact le_trans
    (pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_le_fixedDefect_add_smoothingEnvelope
      hε W hsmall)
    (by linarith)

/-! ## CS9-C: exact nonpositive classification -/

/-- At one fixed transport window, the arbitrary vanishing upper-envelope
contract is equivalent to fixed-defect nonpositivity. -/
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W ↔
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  constructor
  · exact pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_imp_fixedDefect_nonpos W
  · exact pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_of_fixedDefect_nonpos W

/-! ## CS9-D: zero-side strength classification -/

/-- After importing the already established zero-side nonnegativity only for
classification, the envelope contract is equivalent to fixed-defect zero.
This theorem is not an arithmetic proof of the envelope. -/
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_fixedDefect_eq_zero
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W ↔
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  constructor
  · intro henv
    have hnonpos :=
      pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_imp_fixedDefect_nonpos W henv
    have hnonneg :=
      pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg W.circle_safe
    exact le_antisymm hnonpos hnonneg
  · intro hzero
    apply pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_of_fixedDefect_nonpos W
    exact le_of_eq hzero

/-! ## CS9-E: finite zero-window interpretation -/

/-- On a fixed safe transport window, a vanishing upper-envelope contract is
equivalent to every zero in the associated finite window being critical. -/
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_all_window_zeros_critical
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
        ρ.re = (1 : ℝ) / 2 := by
  rw [pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_fixedDefect_eq_zero,
    pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff W.circle_safe]

end DkMath.RH.CFBRCProjection
