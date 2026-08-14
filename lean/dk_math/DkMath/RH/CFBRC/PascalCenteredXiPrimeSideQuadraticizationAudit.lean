/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinQuadraticGramKernel
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
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
open Filter
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

private theorem continuous_pascalCenteredXiPrimeSideQuadraticizationPHZ
    (σ : ℝ) (X : ℕ) :
    Continuous (fun t : ℝ =>
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge σ t) := by
    change Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hterm : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (pascalSymmetricRectangleRightEdge σ t) n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hz : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge σ t) 0) =
        (fun _ : ℝ => 0) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
        simp
      rw [hz]
      exact continuous_const
    · letI : NeZero (n : ℂ) := ⟨by
        exact_mod_cast hn⟩
      have hnterm : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge σ t) n) =
        (fun t : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^
              (-(pascalSymmetricRectangleRightEdge σ t)))) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
      rw [hnterm]
      convert continuous_const.mul
          ((continuous_const_cpow (n : ℂ)).comp
            (continuous_neg.comp hpath)) using 1
      all_goals (ext t; rfl)
  have hsum : Continuous (fun t : ℝ =>
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleRightEdge σ t) n) := by
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  have heq : (fun t : ℝ =>
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) =
      (fun t : ℝ => ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleRightEdge σ t) n) := by
    funext t
    exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _
  rw [heq]
  exact hsum

theorem pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X)
      volume (-W.rectangle.T) W.rectangle.T := by
  have hprime : IntervalIntegrable
      (fun t : ℝ =>
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))
      volume (-W.rectangle.T) W.rectangle.T :=
    (continuous_pascalCenteredXiPrimeSideQuadraticizationPHZ
      W.rectangle.σ X).intervalIntegrable (μ := volume)
        (-W.rectangle.T) W.rectangle.T
  have hnonprime :=
    intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand
      (h := fun _ : ℂ => (1 : ℂ)) (by fun_prop) W
  have hcorrection : IntervalIntegrable
      (fun t : ℝ =>
        pascalXiArchimedeanLogDeriv
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t) +
        pascalXiElementaryLogDerivCorrection
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))
      volume (-W.rectangle.T) W.rectangle.T := by
    have hscaled := hnonprime.mul_const (-Complex.I)
    apply hscaled.congr
    intro t ht
    simp only [pascalXiNonPrimeRightEdgeIntegrand,
      pascalXiArchimedeanRightEdgeIntegrand,
      pascalXiElementaryRightEdgeIntegrand]
    ring_nf
    simp [Complex.I_sq]
  apply hprime.add hcorrection |>.congr
  intro t ht
  simp only [pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude]
  ring

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

/-- The continuous part of the box feature.  The source amplitude is kept
separate so that its finite-rectangle integrability can be supplied by the
right-edge explicit-formula API. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) (t u : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) ^ 2 *
    Complex.exp
      ((u : ℂ) * pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)

theorem pascalCenteredXiPrimeSideQuadraticization_boxFeature_eq_kernel_mul_amplitude
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u =
      pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t := by
  rfl

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (Function.uncurry
      (pascalCenteredXiPrimeSideQuadraticizationBoxKernel W)) := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W) := by
    unfold pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
      pascalOrdinaryToCentered pascalSymmetricRectangleRightEdge
    fun_prop
  have hnode' : Continuous (fun p : ℝ × ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W p.1) :=
    hnode.comp continuous_fst
  have hu : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hexp : Continuous (fun p : ℝ × ℝ =>
      Complex.exp
        ((p.2 : ℂ) * pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W p.1)) :=
    Complex.continuous_exp.comp (hu.mul hnode')
  change Continuous (fun p : ℝ × ℝ =>
    (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W p.1) ^ 2 *
      Complex.exp
        ((p.2 : ℂ) * pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W p.1))
  exact (hnode'.pow 2).mul hexp

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

/-! ## Gate 4B.4: fixed-Xi top-horizontal box feature -/

/-- The centered top horizontal node.  This is a fixed-Xi source point, not a
right-edge ordinary-zeta point. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopNode
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) : ℂ :=
  pascalOrdinaryToCentered
    (pascalSymmetricRectangleTopEdge x W.rectangle.T)

/-- The totalized fixed-Xi negative logarithmic derivative on the top edge. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopAmplitude
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) : ℂ :=
  pascalCenteredXiNegLogDeriv
    (pascalCenteredXiPrimeSideQuadraticizationTopNode W x)

/-- The continuous Mellin kernel carried by the top horizontal node. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) ^ 2 *
    Complex.exp
      ((v : ℂ) * pascalCenteredXiPrimeSideQuadraticizationTopNode W x)

/-- The fixed-Xi top horizontal source transported into the Mellin box. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v *
    pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x

/-- The top horizontal feature aggregated over the finite horizontal edge. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v

theorem pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_intervalIntegrable
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
  have hboundary :=
    pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
      (h := fun _ : ℂ => (1 : ℂ))
      (differentiable_const (c := (1 : ℂ))) W
  apply hboundary.2.1.congr
  intro x hx
  simp [pascalCenteredXiPrimeSideQuadraticizationTopAmplitude,
    pascalCenteredXiPrimeSideQuadraticizationTopNode,
    pascalCenteredXiWeightedNegLogDeriv]

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationTopNode
    (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (pascalCenteredXiPrimeSideQuadraticizationTopNode W) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationTopNode
    pascalSymmetricRectangleTopEdge pascalOrdinaryToCentered
  fun_prop

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (Function.uncurry
      (pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W)) := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationTopNode W) :=
    continuous_pascalCenteredXiPrimeSideQuadraticizationTopNode W
  have hnode' : Continuous (fun p : ℝ × ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1) :=
    hnode.comp continuous_fst
  have hv : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hexp : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((p.2 : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1)) :=
    Complex.continuous_exp.comp (hv.mul hnode')
  change Continuous (fun p : ℝ × ℝ =>
    (pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1) ^ 2 *
      Complex.exp ((p.2 : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationTopNode W p.1))
  exact (hnode'.pow 2).mul hexp

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel_left
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    Continuous (fun x : ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v) := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationTopNode W) :=
    continuous_pascalCenteredXiPrimeSideQuadraticizationTopNode W
  unfold pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel
  exact (hnode.pow 2).mul
    (Complex.continuous_exp.comp (continuous_const.mul hnode))

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel_right
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    Continuous (fun v : ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v) := by
  have hnode : Continuous
      (fun _ : ℝ => pascalCenteredXiPrimeSideQuadraticizationTopNode W x) :=
    continuous_const
  unfold pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel
  exact (hnode.pow 2).mul
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul hnode))

theorem pascalCenteredXiPrimeSideQuadraticization_topBoxFeature_integrableOn_rectangle
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W))
      (Set.uIoc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ
        Set.uIoc (-ε) ε)
      volume := by
  let A : Set ℝ := Set.uIoc W.rectangle.σ (1 - W.rectangle.σ)
  let B : Set ℝ := Set.uIoc (-ε) ε
  let K : Set (ℝ × ℝ) :=
    Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ Set.uIcc (-ε) ε
  have hamp : IntegrableOn
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W) A volume := by
    exact intervalIntegrable_iff.mp
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_intervalIntegrable W)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℂ)) B volume := by
    exact intervalIntegrable_iff.mp
      (intervalIntegrable_const (μ := volume) (a := -ε) (b := ε))
  have hampProd : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1 * (1 : ℂ))
      (A ×ˢ B) volume := by
    change Integrable
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1 * (1 : ℂ))
      (volume.restrict (A ×ˢ B))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hamp.mul_prod hone
  have hampLift : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1)
      (A ×ˢ B) volume := by
    simpa using hampProd
  have hK : IsCompact K := by
    exact isCompact_uIcc.prod isCompact_uIcc
  have hAK : A ×ˢ B ⊆ K := by
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  have hkernel : ContinuousOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W)) K :=
    (continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W).continuousOn
  have hmul : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W p.1 p.2 *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1)
      (A ×ˢ B) volume :=
    IntegrableOn.continuousOn_mul_of_subset hkernel hampLift
      hK (measurableSet_uIoc.prod measurableSet_uIoc) hAK
  have heq :
      Function.uncurry
          (pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W) =
        (fun p : ℝ × ℝ =>
          pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W p.1 p.2 *
            pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W p.1) := by
    funext p
    rfl
  rw [heq]
  simpa [A, B] using hmul

theorem pascalCenteredXiPrimeSideQuadraticization_topBoxFeature_intervalIntegral_swap
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (hbox :
      IntegrableOn
        (Function.uncurry
          (pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W))
        (Set.uIoc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ
          Set.uIoc (-ε) ε)
        volume) :
    (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
      ∫ v in (-ε)..ε,
        pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v) =
      ∫ v in (-ε)..ε,
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v := by
  exact intervalIntegral_intervalIntegral_swap hbox

theorem pascalCenteredXiPrimeSideQuadraticization_topBoxFeature_integral_eq_weight_mul_amplitude
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v) =
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
        pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
  rw [mellinQuadraticBoxWeight_eq_quadratic_mul_multiplier]
  rw [mellinQuadraticBoxMultiplier_eq_logAverage hε]
  simp only [pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature,
    pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel]
  rw [← intervalIntegral.integral_const_mul]
  conv_rhs =>
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with v
  intro _
  ring_nf

theorem pascalCenteredXiPrimeSideQuadraticization_horizontalBase_eq_normalized_topAggregate
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticHorizontalBase ε W =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v := by
  have hbox :=
    pascalCenteredXiPrimeSideQuadraticization_topBoxFeature_integrableOn_rectangle
      ε W
  have hweight : ∀ x : ℝ,
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge x W.rectangle.T)) =
        mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) := by
    intro x
    exact pascalCenteredXiMellinQuadraticWeight_eq_generic hε
      (pascalCenteredXiPrimeSideQuadraticizationTopNode W x)
  unfold pascalCenteredXiMellinQuadraticHorizontalBase
    pascalCenteredXiTopHorizontalContribution
  calc
    (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge x W.rectangle.T)) *
          pascalCenteredXiNegLogDeriv
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge x W.rectangle.T))) =
      ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        mellinQuadraticBoxWeight ε
            (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x
      rw [hweight]
      simp [pascalCenteredXiPrimeSideQuadraticizationTopAmplitude,
        pascalCenteredXiPrimeSideQuadraticizationTopNode]
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x
      rw [pascalCenteredXiPrimeSideQuadraticization_topBoxFeature_integral_eq_weight_mul_amplitude
        hε W x]
      intro hx
      rfl
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          ∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v := by
      rw [intervalIntegral.integral_const_mul]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v := by
      rw [pascalCenteredXiPrimeSideQuadraticization_topBoxFeature_intervalIntegral_swap
        W hbox]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v := by
      rfl

theorem pascalCenteredXiPrimeSideQuadraticizationTopNode_one_sub_eq_neg_conj
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationTopNode W (1 - x) =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) := by
  apply Complex.ext <;>
    simp [pascalCenteredXiPrimeSideQuadraticizationTopNode,
      pascalSymmetricRectangleTopEdge, pascalOrdinaryToCentered,
      criticalLineCenter]
  all_goals ring

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel_left
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u) := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W) := by
    unfold pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
      pascalOrdinaryToCentered pascalSymmetricRectangleRightEdge
    fun_prop
  have hexp : Continuous (fun t : ℝ =>
      Complex.exp ((u : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
    exact Complex.continuous_exp.comp (continuous_const.mul hnode)
  unfold pascalCenteredXiPrimeSideQuadraticizationBoxKernel
  exact (hnode.pow 2).mul hexp

theorem continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel_right
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    Continuous (fun u : ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u) := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W) := by
    unfold pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
      pascalOrdinaryToCentered pascalSymmetricRectangleRightEdge
    fun_prop
  have hexp : Continuous (fun u : ℝ =>
      Complex.exp ((u : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
    exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  unfold pascalCenteredXiPrimeSideQuadraticizationBoxKernel
  exact (continuous_const.pow 2).mul hexp

/-! The finite `t` integral is continuous in the box parameter.  The
source amplitude is only used through its existing finite-interval
integrability certificate; compactness supplies a uniform bound for the
continuous kernel. -/
theorem pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_continuousOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X)
      (Set.uIcc (-ε) ε) := by
  let A : Set ℝ := Set.uIoc (-W.rectangle.T) W.rectangle.T
  let K : Set (ℝ × ℝ) :=
    Set.uIcc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIcc (-ε) ε
  let μ : Measure ℝ := volume.restrict A
  have hK : IsCompact K := by
    exact isCompact_uIcc.prod isCompact_uIcc
  have hkernelGlobal : Continuous
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationBoxKernel W)) :=
    continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel W
  have hkernel : ContinuousOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationBoxKernel W)) K := by
    exact hkernelGlobal.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hkernel
  have hamp : Integrable
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X) μ := by
    change Integrable
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X)
      (volume.restrict A)
    exact intervalIntegrable_iff.mp
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable W X)
  have hbound : Integrable (fun t : ℝ => C *
      ‖pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t‖) μ := by
    exact hamp.norm.const_mul C
  have hcont :=
    continuousOn_of_dominated
      (μ := μ)
      (s := Set.uIcc (-ε) ε)
      (F := fun u t : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u *
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t)
      (bound := fun t : ℝ => C *
        ‖pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t‖)
      (fun u hu => by
        have hku : ContinuousOn
            (fun t : ℝ => pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u)
            (Set.uIcc (-W.rectangle.T) W.rectangle.T) := by
          have hku' :=
            continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel_left W u
          exact hku'.continuousOn
        have hampOn : IntegrableOn
            (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X)
            A volume := by
          exact hamp
        have hprod : IntegrableOn
            (fun t : ℝ =>
              pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u *
                pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t)
            A volume := by
          exact hampOn.continuousOn_mul_of_subset hku isCompact_uIcc
            measurableSet_uIoc Set.uIoc_subset_uIcc
        exact hprod.aestronglyMeasurable)
      (fun u hu => by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
        have hpair : (t, u) ∈ K := ⟨Set.uIoc_subset_uIcc ht, hu⟩
        calc
          ‖pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u *
              pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t‖ =
              ‖pascalCenteredXiPrimeSideQuadraticizationBoxKernel W t u‖ *
                ‖pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t‖ :=
            norm_mul _ _
          _ ≤ C * ‖pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t‖ := by
            exact mul_le_mul_of_nonneg_right (hC (t, u) hpair) (norm_nonneg _))
      hbound
      (Filter.Eventually.of_forall (fun t => by
        have htu :=
          continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel_right W t
        exact (htu.mul continuous_const).continuousOn))
  have htarget : ContinuousOn
      (fun u : ℝ => ∫ t in A,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u)
      (Set.uIcc (-ε) ε) := by
    simpa [μ, A, pascalCenteredXiPrimeSideQuadraticizationBoxFeature,
      pascalCenteredXiPrimeSideQuadraticizationBoxKernel] using hcont
  have htarget' : ContinuousOn
      (fun u : ℝ => ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u)
      (Set.uIcc (-ε) ε) := by
    have hT : -W.rectangle.T ≤ W.rectangle.T := by
      linarith [W.rectangle.hT]
    have heq :
        (fun u : ℝ => ∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) =
        (fun u : ℝ => ∫ t in A,
          pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) := by
      funext u
      rw [intervalIntegral.integral_of_le hT]
      simp [A, Set.uIoc_of_le hT]
    rw [heq]
    exact htarget
  exact htarget'

theorem pascalCenteredXiPrimeSideQuadraticizationShiftedPlus_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1))
      volume (-ε) ε := by
  have hagg :=
    pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_continuousOn
      ε W X
  have hshift : ContinuousOn
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1)
      (Set.uIcc (-ε) ε) := by
    exact hagg.add continuousOn_const
  have hnorm : ContinuousOn
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1))
      (Set.uIcc (-ε) ε) := by
    exact Complex.continuous_normSq.continuousOn.comp hshift
      (fun _ _ => Set.mem_univ _)
  exact hnorm.intervalIntegrable

theorem pascalCenteredXiPrimeSideQuadraticizationShiftedMinus_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1))
      volume (-ε) ε := by
  have hagg :=
    pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_continuousOn
      ε W X
  have hshift : ContinuousOn
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1)
      (Set.uIcc (-ε) ε) := by
    exact hagg.sub continuousOn_const
  have hnorm : ContinuousOn
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1))
      (Set.uIcc (-ε) ε) := by
    exact Complex.continuous_normSq.continuousOn.comp hshift
      (fun _ _ => Set.mem_univ _)
  exact hnorm.intervalIntegrable

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

theorem pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W (-t) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) := by
  apply Complex.ext <;>
    simp [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode,
      pascalOrdinaryToCentered, pascalSymmetricRectangleRightEdge,
      criticalLineCenter]

inductive PascalCenteredXiPrimeSideQuadraticizationAdjointProviderGap : Prop
  | currentFiniteLedger : PascalCenteredXiPrimeSideQuadraticizationAdjointProviderGap

theorem pascalPrimePowerPHZFiniteUpTo_conj
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalPrimePowerPHZFiniteUpTo X s) := by
  rw [pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum,
    pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum]
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hq0 : q = 0
  · subst q
    simp
  · have harg : ((q : ℂ).arg) ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact ne_of_lt Real.pi_pos
    congr 1
    simpa [Complex.natCast_arg] using
      (Complex.conj_cpow (q : ℂ) (-(starRingEnd ℂ s)) harg)

theorem pascalXiElementaryLogDerivCorrection_conj (s : ℂ) :
    pascalXiElementaryLogDerivCorrection (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalXiElementaryLogDerivCorrection s) := by
  simp [pascalXiElementaryLogDerivCorrection]

theorem pascalXiArchimedeanGammaR_conj (s : ℂ) :
    Complex.Gammaℝ (starRingEnd ℂ s) =
      starRingEnd ℂ (Complex.Gammaℝ s) := by
  unfold Complex.Gammaℝ
  have hpi :
      (Real.pi : ℂ) ^ (-(starRingEnd ℂ s) / 2) =
        starRingEnd ℂ ((Real.pi : ℂ) ^ (-s / 2)) := by
    convert (Complex.conj_cpow (Real.pi : ℂ) (-(starRingEnd ℂ s) / 2)
      (by
        rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
        exact ne_of_lt Real.pi_pos)) using 1 <;>
      simp [map_neg, map_ofNat]
  have hgamma :
      Complex.Gamma ((starRingEnd ℂ s) / 2) =
        starRingEnd ℂ (Complex.Gamma (s / 2)) := by
    have h := Complex.Gamma_conj (s / 2)
    convert h using 1
    congr 1
    rw [map_div₀]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      simp only [map_ofNat]
    rw [htwo]
  rw [hpi, hgamma, map_mul]

theorem pascalXiArchimedeanLogDeriv_conj (s : ℂ) :
    pascalXiArchimedeanLogDeriv (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalXiArchimedeanLogDeriv s) := by
  unfold pascalXiArchimedeanLogDeriv
  rw [logDeriv_apply, logDeriv_apply]
  have hfun :
      (starRingEnd ℂ) ∘ Complex.Gammaℝ ∘ (starRingEnd ℂ) =
        Complex.Gammaℝ := by
    funext z
    rw [Function.comp_apply, Function.comp_apply,
      pascalXiArchimedeanGammaR_conj]
    simp only [starRingEnd_apply, star_star]
  have hderiv := congrFun (deriv_conj_conj (f := Complex.Gammaℝ)) s
  rw [hfun] at hderiv
  simp only [Function.comp_apply] at hderiv
  have hderiv' := congrArg (starRingEnd ℂ) hderiv
  have hderiv'' :
      deriv Complex.Gammaℝ (starRingEnd ℂ s) =
        starRingEnd ℂ (deriv Complex.Gammaℝ s) := by
    simpa using hderiv'.symm
  rw [hderiv'', pascalXiArchimedeanGammaR_conj]
  simp

theorem completedRiemannZeta_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hcs0 : starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg (starRingEnd ℂ) h
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    gammaR_ne_zero_of_pos_re (lt_trans zero_lt_one hs)
  have hcgamma : Complex.Gammaℝ (starRingEnd ℂ s) ≠ 0 := by
    rw [pascalXiArchimedeanGammaR_conj]
    intro h
    apply hgamma
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  have hz : completedRiemannZeta s =
      Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp [hgamma]
  have hzc : completedRiemannZeta (starRingEnd ℂ s) =
      Complex.Gammaℝ (starRingEnd ℂ s) *
        riemannZeta (starRingEnd ℂ s) := by
    rw [riemannZeta_def_of_ne_zero hcs0]
    field_simp [hcgamma]
  rw [hzc, pascalXiArchimedeanGammaR_conj, riemannZeta_conj, hz]
  simp

theorem pascalRiemannXiKernel_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    pascalRiemannXiKernel (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalRiemannXiKernel s) := by
  have hs0 : s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hcs0 : starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg (starRingEnd ℂ) h
  have hcs1 : starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg (starRingEnd ℂ) h
  rw [pascalRiemannXiKernel_eq_mul_completedRiemannZeta hcs0 hcs1,
    pascalRiemannXiKernel_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_conj_of_one_lt_re (by simpa using hs)]
  simp [map_mul, map_sub, map_one]

theorem pascalRiemannXiKernel_conj (s : ℂ) :
    pascalRiemannXiKernel (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalRiemannXiKernel s) := by
  have hf_an : AnalyticOnNhd ℂ pascalRiemannXiKernel Set.univ :=
    differentiable_pascalRiemannXiKernel.differentiableOn.analyticOnNhd
      isOpen_univ
  have hg_an : AnalyticOnNhd ℂ
      (fun z => starRingEnd ℂ (pascalRiemannXiKernel (starRingEnd ℂ z)))
      Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz =>
        (differentiableAt_conj_conj_iff.mpr
          differentiable_pascalRiemannXiKernel.differentiableAt).differentiableWithinAt)
      isOpen_univ
  have hgz (z : ℂ) (hz : 1 < z.re) :
      starRingEnd ℂ (pascalRiemannXiKernel (starRingEnd ℂ z)) =
        pascalRiemannXiKernel z := by
    rw [pascalRiemannXiKernel_conj_of_one_lt_re hz]
    simp
  have heq := hg_an.eqOn_of_preconnected_of_eventuallyEq
    hf_an isPreconnected_univ (Set.mem_univ (2 : ℂ))
    (Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num))
      hgz)
  have h := heq (Set.mem_univ s)
  have hc := congrArg (starRingEnd ℂ) h
  simpa using hc

theorem pascalCenteredRiemannXiKernel_conj (z : ℂ) :
    pascalCenteredRiemannXiKernel (starRingEnd ℂ z) =
      starRingEnd ℂ (pascalCenteredRiemannXiKernel z) := by
  unfold pascalCenteredRiemannXiKernel
  have harg :
      starRingEnd ℂ (criticalLineCenter + z) =
        criticalLineCenter + starRingEnd ℂ z := by
    apply Complex.ext <;>
      simp [criticalLineCenter]
  simp only [← harg, pascalRiemannXiKernel_conj]

theorem pascalCenteredXiNegLogDeriv_conj (z : ℂ) :
    pascalCenteredXiNegLogDeriv (starRingEnd ℂ z) =
      starRingEnd ℂ (pascalCenteredXiNegLogDeriv z) := by
  unfold pascalCenteredXiNegLogDeriv
  rw [logDeriv_apply, logDeriv_apply]
  have hfun :
      (starRingEnd ℂ) ∘ pascalCenteredRiemannXiKernel ∘ (starRingEnd ℂ) =
        pascalCenteredRiemannXiKernel := by
    funext w
    rw [Function.comp_apply, Function.comp_apply,
      pascalCenteredRiemannXiKernel_conj]
    simp only [starRingEnd_apply, star_star]
  have hderiv := congrFun
    (deriv_conj_conj (f := pascalCenteredRiemannXiKernel)) z
  rw [hfun] at hderiv
  simp only [Function.comp_apply] at hderiv
  have hderiv' := congrArg (starRingEnd ℂ) hderiv
  have hderiv'' :
      deriv pascalCenteredRiemannXiKernel (starRingEnd ℂ z) =
        starRingEnd ℂ (deriv pascalCenteredRiemannXiKernel z) := by
    simpa using hderiv'.symm
  rw [hderiv'', pascalCenteredRiemannXiKernel_conj]
  simp

theorem pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_one_sub_eq_neg_conj
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W (1 - x) =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationTopAmplitude
  simp only [pascalCenteredXiPrimeSideQuadraticizationTopNode_one_sub_eq_neg_conj,
    pascalCenteredXiNegLogDeriv_neg, pascalCenteredXiNegLogDeriv_conj]

theorem pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature_one_sub_eq_neg_conj
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W (1 - x) v =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x (-v)) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature
    pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel
  rw [pascalCenteredXiPrimeSideQuadraticizationTopNode_one_sub_eq_neg_conj,
    pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_one_sub_eq_neg_conj]
  have hexp :
      Complex.exp
          ((v : ℂ) * -starRingEnd ℂ
              (pascalCenteredXiPrimeSideQuadraticizationTopNode W x)) =
        starRingEnd ℂ (Complex.exp
          (pascalCenteredXiPrimeSideQuadraticizationTopNode W x * ((-v : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp; ring
  rw [hexp]
  simp only [map_pow, map_mul]
  ring_nf

theorem pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_neg_eq_neg_conj
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W (-v) =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature
  calc
    (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x (-v)) =
      ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W (1 - x) (-v) := by
          rw [intervalIntegral.integral_comp_sub_left
            (f := fun x : ℝ =>
              pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x (-v))
            (d := 1)]
          congr 1
          all_goals ring
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        -starRingEnd ℂ
          (pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with x hx
          simpa only [neg_neg] using
            (pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature_one_sub_eq_neg_conj
              W x (-v))
    _ = -starRingEnd ℂ
        (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v) := by
          simp only [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]

noncomputable def pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  -Complex.I *
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v

theorem pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate
  rw [pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_neg_eq_neg_conj]
  simp [map_mul]

theorem pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_continuousOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W)
      (Set.uIcc (-ε) ε) := by
  let A : Set ℝ := Set.uIoc W.rectangle.σ (1 - W.rectangle.σ)
  let K : Set (ℝ × ℝ) :=
    Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) ×ˢ Set.uIcc (-ε) ε
  let μ : Measure ℝ := volume.restrict A
  have hK : IsCompact K := by
    exact isCompact_uIcc.prod isCompact_uIcc
  have hkernelGlobal : Continuous
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W)) :=
    continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W
  have hkernel : ContinuousOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W)) K :=
    hkernelGlobal.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hkernel
  have hamp : Integrable
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W) μ := by
    change Integrable
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W)
      (volume.restrict A)
    exact intervalIntegrable_iff.mp
      (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_intervalIntegrable W)
  have hbound : Integrable (fun x : ℝ => C *
      ‖pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x‖) μ := by
    exact hamp.norm.const_mul C
  have hcont :=
    continuousOn_of_dominated
      (μ := μ)
      (s := Set.uIcc (-ε) ε)
      (F := fun v x : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v *
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x)
      (bound := fun x : ℝ => C *
        ‖pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x‖)
      (fun v hv => by
        have hkv : ContinuousOn
            (fun x : ℝ =>
              pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v)
            (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
          exact continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel_left
            W v |>.continuousOn
        have hampOn : IntegrableOn
            (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W)
            A volume := by
          exact hamp
        have hprod : IntegrableOn
            (fun x : ℝ =>
              pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v *
                pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x)
            A volume := by
          exact hampOn.continuousOn_mul_of_subset hkv isCompact_uIcc
            measurableSet_uIoc Set.uIoc_subset_uIcc
        exact hprod.aestronglyMeasurable)
      (fun v hv => by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        have hpair : (x, v) ∈ K := ⟨Set.uIoc_subset_uIcc hx, hv⟩
        calc
          ‖pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v *
              pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x‖ =
              ‖pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v‖ *
                ‖pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x‖ :=
            norm_mul _ _
          _ ≤ C * ‖pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x‖ := by
            exact mul_le_mul_of_nonneg_right (hC (x, v) hpair) (norm_nonneg _))
      hbound
      (Filter.Eventually.of_forall (fun x => by
        have hku :=
          continuous_pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel_right W x
        exact (hku.mul continuous_const).continuousOn))
  have htarget : ContinuousOn
      (fun v : ℝ => ∫ x in A,
        pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v)
      (Set.uIcc (-ε) ε) := by
    simpa [μ, A, pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature,
      pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel] using hcont
  have htarget' : ContinuousOn
      (fun v : ℝ => ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v)
      (Set.uIcc (-ε) ε) := by
    have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
      linarith [W.rectangle.hσ]
    have heq :
        (fun v : ℝ => ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v) =
        (fun v : ℝ => -∫ x in A,
          pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v) := by
      funext v
      rw [intervalIntegral.integral_of_ge hσ]
      simp [A, Set.uIoc_of_ge hσ]
    rw [heq]
    exact htarget.neg
  exact htarget'

noncomputable def pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v +
    pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v)) / 2

theorem pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature_neg
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W (-v) =
      pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v := by
  unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
  rw [neg_neg]
  ring

theorem pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
    simp only [map_ofNat]
  rw [map_div₀, htwo, map_add,
    ← pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate_neg_eq_conj
      W v,
    ← pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate_neg_eq_conj
      W (-v)]
  simp only [neg_neg]
  ring

theorem pascalCenteredXiPrimeSideQuadraticization_horizontalSymmetricFeature_average_eq_deorientedHorizontalBase
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v =
      -Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W := by
  have htop := pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_continuousOn
    ε W
  have htopInt : IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W)
      volume (-ε) ε :=
    htop.intervalIntegrable
  have hdeoriented : IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W)
      volume (-ε) ε := by
    have hcont : ContinuousOn
        (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W)
        (Set.uIcc (-ε) ε) := by
      exact continuousOn_const.mul htop
    exact hcont.intervalIntegrable
  have hdeorientedNeg : IntervalIntegrable
      (fun v : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v))
      volume (-ε) ε := by
    simpa only [neg_neg] using
      ((IntervalIntegrable.iff_comp_neg (f :=
        pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W)
        (a := -ε) (b := ε)).mp hdeoriented).symm
  have hneg :
      (∫ v in (-ε)..ε,
        pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v)) =
      ∫ v in (-ε)..ε,
        pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W)
        (a := -ε) (b := ε))
  calc
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        (((∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v) +
          ∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v)) / 2) := by
          congr 1
          unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
          rw [intervalIntegral.integral_div]
          congr 1
          exact intervalIntegral.integral_add hdeoriented hdeorientedNeg
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v := by
          rw [hneg]
          ring
    _ = -Complex.I *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v) := by
          unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate
          rw [intervalIntegral.integral_const_mul]
          ring
    _ = -Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W := by
          simp [pascalCenteredXiPrimeSideQuadraticization_horizontalBase_eq_normalized_topAggregate hε W]

theorem pascalSymmetricRectangleRightEdge_neg_eq_conj
    (σ t : ℝ) :
    pascalSymmetricRectangleRightEdge σ (-t) =
      starRingEnd ℂ (pascalSymmetricRectangleRightEdge σ t) := by
  apply Complex.ext <;>
    simp [pascalSymmetricRectangleRightEdge]

theorem pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X (-t) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude
  rw [pascalSymmetricRectangleRightEdge_neg_eq_conj,
    pascalPrimePowerPHZFiniteUpTo_conj,
    pascalXiArchimedeanLogDeriv_conj,
    pascalXiElementaryLogDerivCorrection_conj]
  simp only [map_add]

theorem pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity W X (-t) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity W X t) := by
  simp only [pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity,
    pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode_neg_eq_conj,
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_neg_eq_conj,
    starRingEnd_apply, map_mul]

theorem pascalCenteredXiPrimeSideQuadraticizationGramFeature_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (t u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationGramFeature W (-t) u =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationGramFeature W t u) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationGramFeature
  rw [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode_neg_eq_conj]
  have hexp :
      Complex.exp ((u : ℂ) *
          starRingEnd ℂ
            (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) =
        starRingEnd ℂ
          (Complex.exp ((u : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
    calc
      _ = Complex.exp
          (starRingEnd ℂ ((u : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
              congr 1
              simp [map_mul]
      _ = _ := by exact Complex.exp_conj _
  rw [hexp]
  simp only [starRingEnd_apply, map_mul]

theorem pascalCenteredXiPrimeSideQuadraticizationBoxFeature_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X (-t) u =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) := by
  rw [pascalCenteredXiPrimeSideQuadraticizationBoxFeature_eq_coefficient_mul_feature,
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature_eq_coefficient_mul_feature,
    pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity_neg_eq_conj,
    pascalCenteredXiPrimeSideQuadraticizationGramFeature_neg_eq_conj]
  simp only [starRingEnd_apply, map_mul]

theorem pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature
  calc
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X (-t) u := by
          simpa only [neg_neg] using
            (intervalIntegral.integral_comp_neg
              (f := fun t : ℝ =>
                pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u)
              (a := -W.rectangle.T) (b := W.rectangle.T)).symm
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
        starRingEnd ℂ
          (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          exact pascalCenteredXiPrimeSideQuadraticizationBoxFeature_neg_eq_conj W X t u
    _ = starRingEnd ℂ
        (∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) := by
          rw [intervalIntegral.intervalIntegral_conj]

/-! A concrete mirrored source for the adjoint contract.  Its definition uses
the finite source family itself, with the contour reflection `t ↦ -t`; it is
not defined by applying complex conjugation to the aggregate. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X (-t) u

theorem pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature W X u =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature
    pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature
  calc
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X (-t) u) =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u := by
          simpa only [neg_neg] using
            (intervalIntegral.integral_comp_neg
              (f := fun t : ℝ =>
                pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u)
              (a := -W.rectangle.T) (b := W.rectangle.T))
    _ = starRingEnd ℂ
        (∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) := by
          exact pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_eq_conj
            W X u

/-! Unlike the legacy audit structure above, this contract records the
concrete mirrored finite source and its independently proved conjugation
identity. -/
structure PascalCenteredXiPrimeSideQuadraticizationSourceDerivedAdjointProvider
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) where
  adjoint : ℝ → ℂ
  adjoint_eq_mirrored_source :
    ∀ u,
      adjoint u =
        pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature W X u
  mirrored_source_eq_conj_aggregated :
    ∀ u,
      pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature W X u =
        starRingEnd ℂ
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u)

theorem PascalCenteredXiPrimeSideQuadraticizationSourceDerivedAdjointProvider.adjoint_eq_conj_aggregated
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (P : PascalCenteredXiPrimeSideQuadraticizationSourceDerivedAdjointProvider W X)
    (u : ℝ) :
    P.adjoint u =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) := by
  rw [P.adjoint_eq_mirrored_source, P.mirrored_source_eq_conj_aggregated]

noncomputable def pascalCenteredXiPrimeSideQuadraticizationSourceDerivedAdjointProvider
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    PascalCenteredXiPrimeSideQuadraticizationSourceDerivedAdjointProvider W X :=
  { adjoint := fun u =>
      pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature W X u
    adjoint_eq_mirrored_source := fun _ => rfl
    mirrored_source_eq_conj_aggregated := fun u =>
      pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature_eq_conj
        W X u }

noncomputable def pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u)

/-! ## Gate 4B.3c4: source products and polarization -/

/- The product of the aggregate and its concrete reflected finite source. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u *
    pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature W X u

theorem pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation_eq_normSq
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation W X u =
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) : ℂ) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation
  rw [pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature_eq_conj]
  rw [Complex.normSq_eq_conj_mul_self]
  ring

theorem pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation_integral_eq_gramEnergy
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy ε W X : ℂ) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation W X u := by
  calc
    (pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy ε W X : ℂ) =
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) : ℂ) := by
      unfold pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy
      push_cast
      rw [← intervalIntegral.integral_ofReal]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation W X u := by
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with u hu
      exact (pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation_eq_normSq
        W X u).symm

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

/-- The normalized square energy obtained from the `+1` polarization shift. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1)

/-- The normalized square energy obtained from the `-1` polarization shift. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1)

theorem pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X := by
  unfold pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass :
      0 ≤ ∫ u in (-ε)..ε,
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun u => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

theorem pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X := by
  unfold pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass :
      0 ≤ ∫ u in (-ε)..ε,
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun u => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

/-- The zero/vacuum section paired with the constant reference feature. -/
noncomputable def mellinQuadraticBoxZeroSection (ε : ℝ) (z : ℂ) : ℂ :=
  z * mellinQuadraticBoxMultiplier ε z

theorem mellinQuadraticBoxWeight_eq_node_mul_zeroSection
    (ε : ℝ) (z : ℂ) :
    mellinQuadraticBoxWeight ε z =
      z * mellinQuadraticBoxZeroSection ε z := by
  unfold mellinQuadraticBoxWeight mellinQuadraticBoxZeroSection
  ring

theorem mellinQuadraticBoxZeroSection_eq_normalized_exp_average
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    mellinQuadraticBoxZeroSection ε z =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε, z * Complex.exp ((u : ℂ) * z) := by
  unfold mellinQuadraticBoxZeroSection
  rw [mellinQuadraticBoxMultiplier_eq_logAverage hε]
  calc
    z * (((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε, Complex.exp ((u : ℂ) * z)) =
      z * ∫ u in (-ε)..ε,
        ((2 * ε : ℝ)⁻¹ : ℂ) * Complex.exp ((u : ℂ) * z) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in (-ε)..ε,
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          (z * Complex.exp ((u : ℂ) * z)) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with u hu
          ring
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε, z * Complex.exp ((u : ℂ) * z) := by
          rw [intervalIntegral.integral_const_mul]

theorem pascalCenteredXiPrimeSideQuadraticization_polarization_pointwise
    {F : ℂ} (hF : F = starRingEnd ℂ F) :
    (4 : ℂ) * F =
      (Complex.normSq (F + 1) : ℂ) - (Complex.normSq (F - 1) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self,
    map_add, map_sub, map_one, ← hF]
  ring

theorem pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_polarization_pointwise
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    (4 : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u =
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) : ℂ) -
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) : ℂ) := by
  apply pascalCenteredXiPrimeSideQuadraticization_polarization_pointwise
  exact pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_eq_conj W X u

theorem pascalCenteredXiPrimeSideQuadraticization_boxFeature_intervalIntegral_swap
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hbox :
      IntegrableOn
        (Function.uncurry
          (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X))
        (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
        volume) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      ∫ u in (-ε)..ε,
        pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u) =
      ∫ u in (-ε)..ε,
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u := by
  exact intervalIntegral_intervalIntegral_swap hbox

theorem pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate_of_rectangle_integrable
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hbox :
      IntegrableOn
        (Function.uncurry
          (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X))
        (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
        volume) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
  calc
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          exact
            (pascalCenteredXiPrimeSideQuadraticization_boxFeature_integral_eq_weight_mul_amplitude
              hε W X t).symm
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          ∫ u in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u := by
          rw [intervalIntegral.integral_const_mul]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          ∫ t in (-W.rectangle.T)..W.rectangle.T,
            pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X t u := by
          rw [pascalCenteredXiPrimeSideQuadraticization_boxFeature_intervalIntegral_swap
            W X hbox]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
          rfl

/-! ## Gate P2-A: finite rectangle certificate -/

/-- The `t`-only source amplitude lifts to the finite product rectangle. -/
theorem pascalCenteredXiPrimeSideQuadraticization_verticalAmplitude_product_integrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
          (1 : ℂ))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
      volume := by
  have ht : Integrable
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X)
      (volume.restrict (Set.uIoc (-W.rectangle.T) W.rectangle.T)) :=
    (intervalIntegrable_iff.mp
      (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable W X))
  have hu : Integrable (fun _ : ℝ => (1 : ℂ))
      (volume.restrict (Set.uIoc (-ε) ε)) := by
    exact intervalIntegrable_iff.mp
      (intervalIntegrable_const (μ := volume) (a := -ε) (b := ε) :
        IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume (-ε) ε)
  change Integrable
    (fun p : ℝ × ℝ =>
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
        (1 : ℂ))
    (volume.restrict
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact ht.mul_prod hu

/-- The complete box feature is integrable on every finite rectangle.  The
kernel is continuous on a compact closed rectangle, while the source
amplitude is supplied by the finite right-edge interval certificate above. -/
theorem pascalCenteredXiPrimeSideQuadraticization_boxFeature_integrableOn_rectangle
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-ε) ε)
      volume := by
  let A : Set ℝ := Set.uIoc (-W.rectangle.T) W.rectangle.T
  let B : Set ℝ := Set.uIoc (-ε) ε
  let K : Set (ℝ × ℝ) :=
    Set.uIcc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIcc (-ε) ε
  have hamp : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
          (1 : ℂ))
      (A ×ˢ B) volume := by
    simpa only [A, B] using
      pascalCenteredXiPrimeSideQuadraticization_verticalAmplitude_product_integrable
        ε W X
  have hK : IsCompact K := by
    exact (isCompact_uIcc.prod isCompact_uIcc)
  have hABK : A ×ˢ B ⊆ K := by
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  have hmul : IntegrableOn
      (fun p : ℝ × ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationBoxKernel W p.1 p.2 *
          (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1 *
            (1 : ℂ)))
      (A ×ˢ B) volume :=
    IntegrableOn.continuousOn_mul_of_subset
      (continuous_pascalCenteredXiPrimeSideQuadraticizationBoxKernel W).continuousOn
      hamp hK (measurableSet_uIoc.prod measurableSet_uIoc) hABK
  have heq :
      Function.uncurry
          (pascalCenteredXiPrimeSideQuadraticizationBoxFeature W X) =
        (fun p : ℝ × ℝ =>
          pascalCenteredXiPrimeSideQuadraticizationBoxKernel W p.1 p.2 *
            pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X p.1) := by
    funext p
    rfl
  rw [heq]
  simpa only [A, B, mul_one] using hmul

theorem pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T,
      mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
  exact
    pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate_of_rectangle_integrable
      hε W X
      (pascalCenteredXiPrimeSideQuadraticization_boxFeature_integrableOn_rectangle
        ε W X)

theorem pascalCenteredXiPrimeSideQuadraticization_deorientedVerticalIntegrand_eq_legacy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand ε W X t =
      pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand ε W X t := by
  rw [pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand,
    pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand_eq_weight_mul_decomposed
      ε W X t,
    ← pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
  simp only [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode,
    pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude]

theorem pascalCenteredXiMellinQuadraticComplexVerticalSurface_eq_normalized_aggregate
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
  have hnode : Continuous
      (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W) := by
    unfold pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
      pascalOrdinaryToCentered
    change Continuous (fun t : ℝ =>
      ((W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I) - criticalLineCenter)
    fun_prop
  have hweight : Continuous (fun t : ℝ =>
      mellinQuadraticBoxWeight ε
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
    have hlegacy : Continuous
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0) :=
      (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε).continuous
    have heq : (fun t : ℝ =>
        mellinQuadraticBoxWeight ε
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) =
        (fun t : ℝ =>
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
      funext t
      rw [pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
    rw [heq]
    exact hlegacy.comp hnode
  have hprime : IntervalIntegrable
      (pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand ε W X)
      volume (-W.rectangle.T) W.rectangle.T := by
    have hphz :=
      (continuous_pascalCenteredXiPrimeSideQuadraticizationPHZ
        W.rectangle.σ X).intervalIntegrable (μ := volume)
          (-W.rectangle.T) W.rectangle.T
    have hmul := hphz.continuousOn_mul hweight.continuousOn
    apply hmul.congr
    intro t ht
    dsimp
    rw [← pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
    simpa only [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode] using
      (pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand_eq ε W X t).symm
  have harchAmplitude : IntervalIntegrable
      (fun t : ℝ =>
        pascalXiArchimedeanLogDeriv
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))
      volume (-W.rectangle.T) W.rectangle.T := by
    have harch := intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand
      (h := fun _ : ℂ => (1 : ℂ)) (by fun_prop) W
    have hscaled := harch.mul_const (-Complex.I)
    apply hscaled.congr
    intro t ht
    simp only [pascalXiArchimedeanRightEdgeIntegrand]
    ring_nf
    simp [Complex.I_sq]
  have helemAmplitude : IntervalIntegrable
      (fun t : ℝ =>
        pascalXiElementaryLogDerivCorrection
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))
      volume (-W.rectangle.T) W.rectangle.T := by
    have helem := intervalIntegrable_pascalXiElementaryRightEdgeIntegrand
      (h := fun _ : ℂ => (1 : ℂ)) (by fun_prop) W
    have hscaled := helem.mul_const (-Complex.I)
    apply hscaled.congr
    intro t ht
    simp only [pascalXiElementaryRightEdgeIntegrand]
    ring_nf
    simp [Complex.I_sq]
  have harch : IntervalIntegrable
      (pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand ε W)
      volume (-W.rectangle.T) W.rectangle.T := by
    have hmul := harchAmplitude.continuousOn_mul hweight.continuousOn
    apply hmul.congr
    intro t ht
    dsimp
    rw [← pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
    simpa only [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode] using
      (pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand_eq ε W t).symm
  have helem : IntervalIntegrable
      (pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand ε W)
      volume (-W.rectangle.T) W.rectangle.T := by
    have hmul := helemAmplitude.continuousOn_mul hweight.continuousOn
    apply hmul.congr
    intro t ht
    dsimp
    rw [← pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
    simpa only [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode] using
      (pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand_eq ε W t).symm
  calc
    pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
        pascalCenteredXiMellinQuadraticPrimeDeorientedSurface ε W X +
            pascalCenteredXiMellinQuadraticArchimedeanDeorientedSurface ε W +
          pascalCenteredXiMellinQuadraticElementaryDeorientedSurface ε W := by
      symm
      exact pascalCenteredXiMellinQuadraticDeorientedSurfaces_eq_complexVerticalSurface
        ε W X
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand ε W X t := by
      unfold pascalCenteredXiMellinQuadraticPrimeDeorientedSurface
        pascalCenteredXiMellinQuadraticArchimedeanDeorientedSurface
        pascalCenteredXiMellinQuadraticElementaryDeorientedSurface
        pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand
      rw [← intervalIntegral.integral_add hprime harch,
        ← intervalIntegral.integral_add (hprime.add harch) helem]
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideQuadraticizationDeorientedVerticalIntegrand ε W X t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      exact (pascalCenteredXiPrimeSideQuadraticization_deorientedVerticalIntegrand_eq_legacy
        hε W X t).symm
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
      exact pascalCenteredXiPrimeSideQuadraticization_weighted_source_eq_normalized_aggregate
        hε W X

/-! P2-A and the finite vertical aggregate bridge are now concrete.  The
top-horizontal and radial terms remain outside this vertical identity, and no
prime-side sign or RH consequence is asserted. -/

theorem pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference_of_integrable
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hplus : IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1))
      volume (-ε) ε)
    (hminus : IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1))
      volume (-ε) ε) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X : ℂ) := by
  have hpol :
      (fun u : ℝ =>
        (4 : ℂ) *
          pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) =
      (fun u : ℝ =>
        (Complex.normSq
            (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) : ℂ) -
          (Complex.normSq
            (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) : ℂ)) := by
    funext u
    exact pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_polarization_pointwise
      W X u
  calc
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
        (4 : ℂ) *
          (((2 * ε : ℝ)⁻¹ : ℂ) *
            ∫ u in (-ε)..ε,
              pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u) := by
      rw [pascalCenteredXiMellinQuadraticComplexVerticalSurface_eq_normalized_aggregate hε]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          (4 : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          ((Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) : ℂ) -
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) : ℂ)) := by
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with u hu
      exact congrFun hpol u
    _ = (pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X : ℂ) := by
      have hplusC : IntervalIntegrable
          (fun u : ℝ =>
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) : ℂ))
          volume (-ε) ε := by
        have h1 := Complex.ofRealCLM.integrable_comp hplus.1
        have h2 := Complex.ofRealCLM.integrable_comp hplus.2
        exact ⟨by
            change Integrable
              (fun u : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) : ℂ))
              (volume.restrict (Set.Ioc (-ε) ε))
            simpa [Function.comp_def] using h1,
          by
            change Integrable
              (fun u : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1) : ℂ))
              (volume.restrict (Set.Ioc ε (-ε)))
            simpa [Function.comp_def] using h2⟩
      have hminusC : IntervalIntegrable
          (fun u : ℝ =>
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) : ℂ))
          volume (-ε) ε := by
        have h1 := Complex.ofRealCLM.integrable_comp hminus.1
        have h2 := Complex.ofRealCLM.integrable_comp hminus.2
        exact ⟨by
            change Integrable
              (fun u : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) : ℂ))
              (volume.restrict (Set.Ioc (-ε) ε))
            simpa [Function.comp_def] using h1,
          by
            change Integrable
              (fun u : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1) : ℂ))
              (volume.restrict (Set.Ioc ε (-ε)))
            simpa [Function.comp_def] using h2⟩
      rw [intervalIntegral.integral_sub hplusC hminusC]
      unfold pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy
        pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy
      simp only [Complex.ofReal_mul]
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal]
      ring_nf
      have hc :
          (↑(2 : ℝ))⁻¹ * (↑ε : ℂ)⁻¹ =
            (↑(ε⁻¹ * (1 / 2 : ℝ)) : ℂ) := by
        norm_num [Complex.ofReal_inv, Complex.ofReal_mul]
        ring
      rw [hc]
      ring

theorem pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg_of_integrable
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hplus : IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1))
      volume (-ε) ε)
    (hminus : IntervalIntegrable
      (fun u : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1))
      volume (-ε) ε) :
    pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X ↔
      0 ≤ (pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X).re := by
  have hid :=
    pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference_of_integrable
      hε W X hplus hminus
  have hreal := congrArg Complex.re hid
  have hreal' :
      4 * (pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X).re =
        pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X -
          pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X := by
    simpa [Complex.mul_re] using hreal
  constructor <;> intro h
  · linarith
  · linarith

theorem pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X : ℂ) := by
  exact pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference_of_integrable
    hε W X
    (pascalCenteredXiPrimeSideQuadraticizationShiftedPlus_intervalIntegrable ε W X)
    (pascalCenteredXiPrimeSideQuadraticizationShiftedMinus_intervalIntegrable ε W X)

theorem pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X ↔
      0 ≤ (pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X).re := by
  exact pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg_of_integrable
    hε W X
    (pascalCenteredXiPrimeSideQuadraticizationShiftedPlus_intervalIntegrable ε W X)
    (pascalCenteredXiPrimeSideQuadraticizationShiftedMinus_intervalIntegrable ε W X)

noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v +
    pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v

theorem pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
  calc
    pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v +
        pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v =
      starRingEnd ℂ
          (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v) +
        starRingEnd ℂ
          (pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v) := by
            congr 1
            · exact pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_eq_conj
                W X v
            · exact pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature_eq_conj
                W v
    _ = starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v +
          pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v) := by
            exact (map_add (starRingEnd ℂ)
              (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v)
              (pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v)).symm

theorem pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_continuousOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X)
      (Set.uIcc (-ε) ε) := by
  unfold pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
  have hvert :=
    pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_continuousOn
      ε W X
  have htop :=
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_continuousOn
      ε W
  have hdeoriented : ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W)
      (Set.uIcc (-ε) ε) := by
    exact continuousOn_const.mul htop
  have hdeorientedNeg : ContinuousOn
      (fun v : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v))
      (Set.uIcc (-ε) ε) := by
    apply hdeoriented.comp continuous_neg.continuousOn
    intro v hv
    simp only [Set.mem_uIcc] at hv ⊢
    rcases hv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hsymmetric : ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W)
      (Set.uIcc (-ε) ε) := by
    unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
    exact (hdeoriented.add hdeorientedNeg).div_const 2
  exact hvert.add hsymmetric

theorem pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X)
      volume (-ε) ε := by
  exact (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_continuousOn
    ε W X).intervalIntegrable

theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_normalized_wholeBoxFeature
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v := by
  have hvert : IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X)
      volume (-ε) ε :=
    (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_continuousOn
      ε W X).intervalIntegrable
  have htop :=
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature_continuousOn
      ε W
  have hdeoriented : ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W)
      (Set.uIcc (-ε) ε) := by
    exact continuousOn_const.mul htop
  have hdeorientedNeg : ContinuousOn
      (fun v : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v))
      (Set.uIcc (-ε) ε) := by
    apply hdeoriented.comp continuous_neg.continuousOn
    intro v hv
    simp only [Set.mem_uIcc] at hv ⊢
    rcases hv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hsymmetric : ContinuousOn
      (pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W)
      (Set.uIcc (-ε) ε) := by
    unfold pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
    exact (hdeoriented.add hdeorientedNeg).div_const 2
  have hsymmetricInt : IntervalIntegrable
      (pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W)
      volume (-ε) ε := hsymmetric.intervalIntegrable
  calc
    pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
        pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X -
          Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W := rfl
    _ = (((2 * ε : ℝ)⁻¹ : ℂ) *
          (∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v)) +
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          (∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v)) := by
      have hh :=
        pascalCenteredXiPrimeSideQuadraticization_horizontalSymmetricFeature_average_eq_deorientedHorizontalBase
          hε W
      rw [pascalCenteredXiMellinQuadraticComplexVerticalSurface_eq_normalized_aggregate
        hε W X]
      calc
        (((2 * ε : ℝ)⁻¹ : ℂ) *
              (∫ v in (-ε)..ε,
                pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v) -
            Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W) =
          ((2 * ε : ℝ)⁻¹ : ℂ) *
              (∫ v in (-ε)..ε,
                pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v) +
            (-Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W) := by
              ring
        _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
              (∫ v in (-ε)..ε,
                pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v) +
            ((2 * ε : ℝ)⁻¹ : ℂ) *
              (∫ v in (-ε)..ε,
                pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v) := by
              rw [← hh]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
          (((∫ v in (-ε)..ε,
              pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v) +
            ∫ v in (-ε)..ε,
              pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v)) := by
      ring
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v +
              pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v) := by
      rw [intervalIntegral.integral_add hvert hsymmetricInt]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v := by
      rfl

theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      starRingEnd ℂ
        (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X) := by
  rw [pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_normalized_wholeBoxFeature
    hε W X]
  have hwhole := pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_intervalIntegrable
    ε W X
  calc
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          starRingEnd ℂ
            (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v) := by
          congr 1
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with v hv
          exact pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_eq_conj W X v
    _ = starRingEnd ℂ
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ v in (-ε)..ε,
            pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v) := by
          have hscale :
              starRingEnd ℂ ((2 * ε : ℝ)⁻¹ : ℂ) =
                ((2 * ε : ℝ)⁻¹ : ℂ) := by
            have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
              simp only [map_ofNat]
            simp [map_inv₀, htwo, Complex.ofReal_mul]
          simp only [map_mul, hscale, intervalIntegral.intervalIntegral_conj]

theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_scalarSurface
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      (pascalCenteredXiMellinQuadraticScalarSurface ε W X : ℂ) := by
  apply Complex.ext
  · exact pascalCenteredXiMellinQuadraticComplexWholeSurface_re_eq_scalarSurface
      hε W X
  · have hconj := pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_conj hε W X
    have him := congrArg Complex.im hconj
    have him' :
        (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im =
          -(pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im := by
      exact (show
        (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im =
          -(pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im by
        change (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im =
          -(pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im at him
        exact him)
    have hz :
        (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).im = 0 := by
      linarith [him']
    simpa using hz

/-! ## Q2-K: whole shifted energies and polarization -/

/- The whole shifted energies are deliberately distinct from the earlier
vertical-only energies.  Their feature contains the source-derived horizontal
symmetrization as well as the vertical aggregate. -/
noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ v in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1)

noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ v in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1)

theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlus_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun v : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1))
      volume (-ε) ε := by
  have hwhole := pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_continuousOn
    ε W X
  have hshift : ContinuousOn
      (fun v : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1)
      (Set.uIcc (-ε) ε) := by
    exact hwhole.add continuousOn_const
  have hnorm : ContinuousOn
      (fun v : ℝ => Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1))
      (Set.uIcc (-ε) ε) := by
    exact Complex.continuous_normSq.continuousOn.comp hshift
      (fun _ _ => Set.mem_univ _)
  exact hnorm.intervalIntegrable

theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinus_intervalIntegrable
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun v : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1))
      volume (-ε) ε := by
  have hwhole := pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_continuousOn
    ε W X
  have hshift : ContinuousOn
      (fun v : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1)
      (Set.uIcc (-ε) ε) := by
    exact hwhole.sub continuousOn_const
  have hnorm : ContinuousOn
      (fun v : ℝ => Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1))
      (Set.uIcc (-ε) ε) := by
    exact Complex.continuous_normSq.continuousOn.comp hshift
      (fun _ _ => Set.mem_univ _)
  exact hnorm.intervalIntegrable

theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X := by
  unfold pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass :
      0 ≤ ∫ v in (-ε)..ε,
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun v => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

theorem pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X := by
  unfold pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass :
      0 ≤ ∫ v in (-ε)..ε,
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun v => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

theorem pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_polarization_pointwise
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) :
    (4 : ℂ) *
        pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v =
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ) -
      (Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ) := by
  apply pascalCenteredXiPrimeSideQuadraticization_polarization_pointwise
  exact pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_eq_conj W X v

theorem pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference_of_integrable
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hplus : IntervalIntegrable
      (fun v : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1))
      volume (-ε) ε)
    (hminus : IntervalIntegrable
      (fun v : ℝ =>
        Complex.normSq
          (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1))
      volume (-ε) ε) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X : ℂ) := by
  have hpol :
      (fun v : ℝ =>
        (4 : ℂ) *
          pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v) =
      (fun v : ℝ =>
        (Complex.normSq
            (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ) -
          (Complex.normSq
            (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ)) := by
    funext v
    exact pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_polarization_pointwise
      W X v
  calc
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
        (4 : ℂ) *
          (((2 * ε : ℝ)⁻¹ : ℂ) *
            ∫ v in (-ε)..ε,
              pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v) := by
      rw [pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_normalized_wholeBoxFeature
        hε W X]
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          (4 : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ v in (-ε)..ε,
          ((Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ) -
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ)) := by
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with v hv
      exact congrFun hpol v
    _ = (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X : ℂ) := by
      have hplusC : IntervalIntegrable
          (fun v : ℝ =>
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ))
          volume (-ε) ε := by
        have h1 := Complex.ofRealCLM.integrable_comp hplus.1
        have h2 := Complex.ofRealCLM.integrable_comp hplus.2
        exact ⟨by
            change Integrable
              (fun v : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ))
              (volume.restrict (Set.Ioc (-ε) ε))
            simpa [Function.comp_def] using h1,
          by
            change Integrable
              (fun v : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v + 1) : ℂ))
              (volume.restrict (Set.Ioc ε (-ε)))
            simpa [Function.comp_def] using h2⟩
      have hminusC : IntervalIntegrable
          (fun v : ℝ =>
            (Complex.normSq
              (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ))
          volume (-ε) ε := by
        have h1 := Complex.ofRealCLM.integrable_comp hminus.1
        have h2 := Complex.ofRealCLM.integrable_comp hminus.2
        exact ⟨by
            change Integrable
              (fun v : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ))
              (volume.restrict (Set.Ioc (-ε) ε))
            simpa [Function.comp_def] using h1,
          by
            change Integrable
              (fun v : ℝ =>
                (Complex.normSq
                  (pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature W X v - 1) : ℂ))
              (volume.restrict (Set.Ioc ε (-ε)))
            simpa [Function.comp_def] using h2⟩
      rw [intervalIntegral.integral_sub hplusC hminusC]
      unfold pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy
        pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy
      simp only [Complex.ofReal_mul]
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal]
      ring_nf
      have hc :
          (↑(2 : ℝ))⁻¹ * (↑ε : ℂ)⁻¹ =
            (↑(ε⁻¹ * (1 / 2 : ℝ)) : ℂ) := by
        norm_num [Complex.ofReal_inv, Complex.ofReal_mul]
        ring
      rw [hc]
      ring

theorem pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X : ℂ) -
        (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X : ℂ) := by
  exact pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference_of_integrable
    hε W X
    (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlus_intervalIntegrable ε W X)
    (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinus_intervalIntegrable ε W X)

theorem pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    4 * pascalCenteredXiMellinQuadraticScalarSurface ε W X =
      pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X -
        pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X := by
  have hid := pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference
    hε W X
  have hscalar := pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_scalarSurface hε W X
  have hreal := congrArg Complex.re hid
  rw [hscalar] at hreal
  simpa [Complex.mul_re] using hreal

theorem pascalCenteredXiPrimeSideQuadraticization_wholeShiftedEnergy_order_iff_scalarSurface_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X ↔
      0 ≤ pascalCenteredXiMellinQuadraticScalarSurface ε W X := by
  have hid := pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_shiftedEnergyDifference
    hε W X
  constructor <;> intro h
  · linarith
  · linarith

/-! The vertical-only ordering gap above does not classify the whole
observables.  The whole shifted beams have their own explicit provider gap;
the scalar equivalence is algebraic and is not an independent ordering
theorem. -/
inductive PascalCenteredXiPrimeSideQuadraticizationWholeShiftedEnergyOrderingGap : Prop
  | noIndependentWholeOrderingProvider :
      PascalCenteredXiPrimeSideQuadraticizationWholeShiftedEnergyOrderingGap

/-! The individual shifted beams are PSD, but no independent ordering
provider is present.  The lower-level conditional equivalence and its
unconditional wrapper record that the ordering is exactly the vertical sign;
the interval-integrability certificates come from finite-window continuity. -/
inductive PascalCenteredXiPrimeSideQuadraticizationShiftedEnergyOrderingGap : Prop
  | noIndependentOrderingProvider :
      PascalCenteredXiPrimeSideQuadraticizationShiftedEnergyOrderingGap

/-! ## Q3: radial comparison audit -/

theorem pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_pi_mul_normalizedArithmetic_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticScalarSurface ε W X =
      Real.pi *
        (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re := by
  rw [pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_scalarSurface_div_pi
    hε W X]
  field_simp [Real.pi_ne_zero]

theorem pascalCenteredXiPrimeSideQuadraticization_radial_le_scalarSurface_iff_defect_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiMellinQuadraticScalarSurface ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0 := by
  have hcomp :
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
          pascalCenteredXiMellinQuadraticScalarSurface ε W X ↔
        0 ≤ pascalCenteredXiMellinQuadraticScalarExcess ε W X := by
    unfold pascalCenteredXiMellinQuadraticScalarExcess
    constructor <;> intro h <;> linarith
  rw [hcomp,
    pascalCenteredXiMellinQuadraticScalarExcess_eq_neg_pi_mul_defect hε W X]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- The fixed radial observable is nonnegative on safe radii.  This is a
radial representation fact only; it is not a comparison with the arithmetic
surface. -/
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_nonneg
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 ≤ pascalCenteredXiFixedRadialSecondMomentFunctional R := by
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial hR]
  unfold pascalCriticalMirrorZeroWindowCF2DRadialMass
  apply Finset.sum_nonneg
  intro ρ hρ
  have hmult : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) := by positivity
  have hq2 : 0 ≤
      DkMath.CosmicFormula.Rotation.CF2D.Vec.q2
        (pascalCenteredZeroCF2DState ρ) := by
    rw [pascalCenteredZeroCF2DState_q2_eq_normSq]
    exact Complex.normSq_nonneg _
  exact mul_nonneg hmult hq2

/-! The radial nonnegativity above does not imply the radial comparison:
`0 ≤ radial` and `0 ≤ scalar surface` do not order the two quantities.  The
zero-side fixed-defect and RH-frontier theorems are intentionally not used as
providers for the finite arithmetic inequality. -/
inductive PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap : Prop
  | noIndependentArithmeticToRadialProvider :
      PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap

/-! ## IPSM-029: common centered-Xi source -/

noncomputable def pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight
    (ε : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 * centeredMellinSpectralWeight
    (centeredMellinBoxApprox ε) z

theorem pascalCenteredXiMellinQuadraticZeroMoment_eq_commonSourceMoment
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticZeroMoment ε W =
      pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε)
        W.R := by
  exact pascalCenteredXiMellinSecondDifferenceZeroMoment_tau_zero_eq W

noncomputable def pascalCenteredXiPrimeSideQuadraticizationRadialWeight
    (z : ℂ) : ℂ :=
  (Complex.normSq z : ℂ)

theorem pascalCenteredXiZeroDiskWeightedMoment_radialWeight_eq
    (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment
        pascalCenteredXiPrimeSideQuadraticizationRadialWeight R =
      (pascalCenteredXiZeroDiskRadialSecondMoment R : ℂ) := by
  classical
  unfold pascalCenteredXiZeroDiskWeightedMoment
    pascalCenteredXiPrimeSideQuadraticizationRadialWeight
    pascalCenteredXiZeroDiskRadialSecondMoment
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  norm_num

noncomputable def pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
    (ε : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq z +
    (pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε z).re

theorem pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_eq_commonSourceMoment
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W =
      ∑ a ∈ pascalCenteredXiZeroDiskFinset W.R,
        (pascalCenteredXiZeroMultiplicity a : ℝ) *
          pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight ε a := by
  unfold pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial W.circle_safe,
    ← pascalCenteredXiZeroDiskRadialSecondMoment_eq_window W.R,
    pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_eq,
    pascalCenteredXiMellinQuadraticZeroMoment_eq_commonSourceMoment]
  unfold pascalCenteredXiZeroDiskRadialSecondMoment
    pascalCenteredXiZeroDiskWeightedMoment
    pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
  simp only [Complex.neg_re]
  rw [Complex.re_sum]
  calc
    (∑ z ∈ pascalCenteredXiZeroDiskFinset W.R,
        (pascalCenteredXiZeroMultiplicity z : ℝ) * Complex.normSq z) -
        -(∑ a ∈ pascalCenteredXiZeroDiskFinset W.R,
          ((pascalCenteredXiZeroMultiplicity a : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε a).re) =
      (∑ z ∈ pascalCenteredXiZeroDiskFinset W.R,
        (pascalCenteredXiZeroMultiplicity z : ℝ) * Complex.normSq z) +
        ∑ a ∈ pascalCenteredXiZeroDiskFinset W.R,
          ((pascalCenteredXiZeroMultiplicity a : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε a).re := by ring
    _ = (∑ a ∈ pascalCenteredXiZeroDiskFinset W.R,
        (((pascalCenteredXiZeroMultiplicity a : ℝ) * Complex.normSq a) +
          ((pascalCenteredXiZeroMultiplicity a : ℂ) *
            pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε a).re)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ pascalCenteredXiZeroDiskFinset W.R,
        (pascalCenteredXiZeroMultiplicity a : ℝ) *
          (Complex.normSq a +
            (pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε a).re)) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [Complex.mul_re]
      ring

theorem tendsto_pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight ε z)
      (𝓝[>] 0)
      (nhds (2 * z.re ^ 2)) := by
  have hweight := tendsto_centeredMellinBoxApprox_quadraticWeight z
  have hreal := (Complex.continuous_re.tendsto (z ^ 2)).comp hweight
  have hnorm : Tendsto (fun _ : ℝ => Complex.normSq z) (𝓝[>] 0)
      (nhds (Complex.normSq z)) := tendsto_const_nhds
  have hsum : Tendsto
      (fun ε : ℝ =>
        Complex.normSq z +
          (z ^ 2 * centeredMellinSpectralWeight
            (centeredMellinBoxApprox ε) z).re)
      (𝓝[>] 0)
      (nhds (Complex.normSq z + (z ^ 2).re)) := hnorm.add hreal
  convert hsum using 1
  · funext ε
    rfl
  · simp [Complex.normSq, pow_two, Complex.mul_re]
    ring

theorem pascalCenteredXiFixedDefect_nonpos_of_endpoint_le_vanishingEnvelope
    (W : PascalCenteredXiResidueTransportWindow)
    (r : ℝ → ℝ)
    (hr : Tendsto r (𝓝[>] 0) (nhds 0))
    (hupper : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ r ε) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  exact le_of_tendsto_of_tendsto
    (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon W)
    hr hupper

end DkMath.RH.CFBRCProjection
