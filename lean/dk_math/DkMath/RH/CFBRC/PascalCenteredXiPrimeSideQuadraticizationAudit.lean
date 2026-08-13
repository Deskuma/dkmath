/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinQuadraticGramKernel
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import Mathlib.Tactic

/-!
# Gate 4B.3: prime-side quadraticization audit

This module fixes the exact finite source surfaces that a future
quadraticization provider would have to use.  The fixed `τ = 0` weight is
adapted to the generic Mellin quadratic weight, and the finite prime-side
approximant is exposed as its existing von-Mangoldt mode sum together with
all three correction surfaces.

The source ledger is linear in its arithmetic modes, whereas the generic
Mellin Gram form is a two-index quadratic form.  No coefficient family,
adjoint provider, cancellation theorem, sign theorem, limit exchange, or RH
consequence is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open MeasureTheory
open scoped Interval Topology

/-- The fixed-`τ = 0` RH weight is exactly the generic Mellin quadratic
weight.  This is an adapter theorem only; the Gram diagonal remains a
different two-variable object. -/
theorem pascalCenteredXiMellinQuadraticWeight_eq_generic
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0 z =
      mellinQuadraticBoxWeight ε z := by
  rw [pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
    hε z]
  rfl

/-- One finite von-Mangoldt mode in the prime-side source ledger. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationPrimeMode
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n _X : ℕ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
      Complex.I)

/-- The finite prime-mode sum, before the correction surfaces are added. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (X + 1),
    pascalCenteredXiPrimeSideQuadraticizationPrimeMode ε W n X

/-- The exact finite source ledger: prime modes, archimedean correction,
elementary correction, and top-horizontal correction are all retained. -/
theorem pascalCenteredXiPrimeSideQuadraticization_source_ledger
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
        W.toContourTransportWindow := by
  simpa [pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum,
    pascalCenteredXiPrimeSideQuadraticizationPrimeMode] using
    (pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum
      hε W X)

/-- The current source ledger is a one-index linear mode sum.  This named
surface records the arity boundary against the two-index Gram quadratic form;
it is not an impossibility theorem and does not assert that no future bridge
can exist. -/
theorem pascalCenteredXiPrimeSideQuadraticization_linear_source_boundary
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

end DkMath.RH.CFBRCProjection
