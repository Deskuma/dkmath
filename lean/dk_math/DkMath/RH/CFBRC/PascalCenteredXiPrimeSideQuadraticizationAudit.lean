/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinQuadraticGramKernel
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import Mathlib.MeasureTheory.Integral.Prod
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
      pascalOrdinaryToCentered
    change Continuous (fun t : ℝ =>
      ((W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I) - criticalLineCenter)
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

end DkMath.RH.CFBRCProjection
