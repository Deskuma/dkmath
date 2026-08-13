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

/-! ## Gate 4B.3c0--c2: source-index semantics and the linear box surface -/

/-- The centered spectral node attached to a contour-height coordinate. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) : ℂ :=
  pascalOrdinaryToCentered
    (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

/-- The full finite vertical source amplitude at a fixed contour height.

The arithmetic cutoff, archimedean correction, and elementary correction are
kept in one source-derived amplitude.  The top-horizontal term is deliberately
not folded into this vertical surface. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t) +
    pascalXiArchimedeanLogDeriv
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t) +
    pascalXiElementaryLogDerivCorrection
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

/-- The deoriented vertical source surface before the differential factor
`Complex.I` is inserted. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  mellinQuadraticBoxWeight ε
      (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t

/-- The oriented vertical source surface, with `ds = i dt`. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationVerticalIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand
    ε W X t * Complex.I

/-- Exact factorization of the complete finite vertical source into the
generic one-variable weight and the source-derived amplitude. -/
theorem pascalCenteredXiPrimeSideQuadraticization_deoriented_factorization
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand
        ε W X t =
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
  rfl

/-- The same vertical surface, expanded into its prime, archimedean, and
elementary source terms.  This is an exact finite identity and carries no
positivity statement. -/
theorem pascalCenteredXiPrimeSideQuadraticization_vertical_source_expansion
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationVerticalIntegrand ε W X t =
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) * Complex.I +
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalXiArchimedeanLogDeriv
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) * Complex.I +
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalXiElementaryLogDerivCorrection
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) * Complex.I := by
  rw [pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
  simp only [pascalCenteredXiPrimeSideQuadraticizationVerticalIntegrand,
    pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand,
    pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode,
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude]
  ring

/-- The linear two-variable box feature surface.  Here `u` is the logarithmic
box-average variable; it is not the contour variable `t` or the arithmetic
index `n`. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t u : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) ^ 2 *
    Complex.exp
      ((u : ℂ) * pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t

/-- Exact logarithmic-box expansion of the linear source surface. -/
theorem pascalCenteredXiPrimeSideQuadraticization_boxFeature_integral_eq_weight_mul_amplitude
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) =
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
  rw [mellinQuadraticBoxWeight_eq_quadratic_mul_multiplier]
  rw [mellinQuadraticBoxMultiplier_eq_logAverage hε]
  simp only [pascalCenteredXiPrimeSideQuadraticizationBoxFeature]
  rw [← intervalIntegral.integral_const_mul]
  conv_rhs =>
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with u
  intro _
  ring_nf

/-! ## Gate 4B.3c3: continuous coefficient and feature audit -/

noncomputable def pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t *
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t

noncomputable def pascalCenteredXiPrimeSideQuadraticizationGramFeature
    (W : PascalCenteredXiResidueTransportWindow) (t u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t *
    Complex.exp
      ((u : ℂ) * pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)

theorem pascalCenteredXiPrimeSideQuadraticizationBoxFeature_eq_coefficient_mul_feature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u =
      pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity W X t *
        pascalCenteredXiPrimeSideQuadraticizationGramFeature W t u := by
  simp only [pascalCenteredXiPrimeSideQuadraticizationBoxFeature,
    pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity,
    pascalCenteredXiPrimeSideQuadraticizationGramFeature]
  ring

noncomputable def pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u

noncomputable def pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u)

theorem pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy ε W X := by
  unfold pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass :
      0 ≤ ∫ u in (-ε)..ε,
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun u => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

/-! A future source-derived adjoint must provide the following exact contract.
The existing finite ledger does not instantiate it; defining the conjugate
function alone is not a source-derived provider. -/
structure PascalCenteredXiPrimeSideQuadraticizationContinuousAdjointProvider
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) where
  adjoint : ℝ → ℂ
  source_derived : Prop
  adjoint_eq_conj_aggregated :
    ∀ u,
      adjoint u =
        starRingEnd ℂ
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u)

end DkMath.RH.CFBRCProjection
