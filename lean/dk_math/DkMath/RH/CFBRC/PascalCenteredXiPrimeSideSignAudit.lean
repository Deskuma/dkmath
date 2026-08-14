/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
import Mathlib.Tactic

/-!
# Prime-side sign mechanism audit

This module records the exact real four-term decomposition of the normalized
finite arithmetic surface and the order-preserving adapters needed to carry a
conditional nonpositivity statement through the two ordered limits.

No sign of the prime term, correction terms, or full arithmetic surface is
asserted.  In particular, the eventual nonpositivity hypotheses below are
providers for a later sign audit, not a disguised RH or defect-vanishing
assumption.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gate 1: normalized real four-term surface -/

private noncomputable def pascalCenteredXiPrimeSideSignNormalization : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹

/-- The real part of the normalized finite von Mangoldt right-edge term. -/
noncomputable def pascalCenteredXiMellinQuadraticNormalizedPrimeContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (pascalCenteredXiPrimeSideSignNormalization *
      (2 * (∑ n ∈ Finset.range (X + 1),
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^
                (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
            Complex.I)))).re

/-- The real part of the normalized archimedean correction. -/
noncomputable def pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (pascalCenteredXiPrimeSideSignNormalization *
      (2 * pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T)).re

/-- The real part of the normalized elementary correction. -/
noncomputable def pascalCenteredXiMellinQuadraticNormalizedElementaryContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (pascalCenteredXiPrimeSideSignNormalization *
      (2 * pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T)).re

/-- The real part of the normalized top-horizontal correction. -/
noncomputable def pascalCenteredXiMellinQuadraticNormalizedTopContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (pascalCenteredXiPrimeSideSignNormalization *
      (2 * pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow)).re

/-- The normalized arithmetic approximant has exactly four real components.
The top-horizontal term is retained; no finite-height correction is discarded.
-/
theorem pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re =
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X +
      pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
      pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
      pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W := by
  unfold pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
  rw [pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum hε W X]
  simp only [pascalCenteredXiPrimeSideSignNormalization,
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution,
    pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution,
    pascalCenteredXiMellinQuadraticNormalizedElementaryContribution,
    pascalCenteredXiMellinQuadraticNormalizedTopContribution,
    mul_add, Complex.add_re]

/-! ## Gate 2: ordered-limit sign transport -/

/-- Eventual nonpositivity of the finite cutoff defects survives the fixed-
`ε` cutoff limit.  This is only an order-closedness adapter. -/
theorem pascalCenteredXiArithmeticDefectEndpoint_nonpos_of_eventually_approximant_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (happrox : ∀ᶠ X : ℕ in atTop,
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0 := by
  apply le_of_tendsto
    (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant hε W)
  exact happrox

/-- Eventual nonpositivity of the ordered `ε`-endpoint survives the
`ε → 0+` limit to the fixed Xi defect. -/
theorem pascalCenteredXiFixedDefect_nonpos_of_eventually_endpoint_nonpos
    (W : PascalCenteredXiResidueTransportWindow)
    (hendpoint : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  apply le_of_tendsto
    (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon W)
  exact hendpoint

end DkMath.RH.CFBRCProjection
