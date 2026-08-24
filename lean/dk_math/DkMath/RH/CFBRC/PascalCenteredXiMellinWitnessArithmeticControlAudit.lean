/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit
import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import Mathlib.Tactic

/-!
# GWSS-003A: finite arithmetic control audit

This module transports the corrected finite Mellin witness from GWSS-002D
through the already-proved finite arithmetic explicit formula.  It records
the exact four-term arithmetic right-hand side, the phase forced by the
off-critical detector, and pointwise finite-linearity identities for the
prime, ordinary-zeta, archimedean, elementary, and top-horizontal surfaces.

The phase theorem is bookkeeping: it rewrites the finite explicit formula
using the already-established zero-side detector and therefore is not an
independent arithmetic-control provider.  In particular, the top-horizontal
term is retained, no height limit is taken, and no estimate, sign theorem, or
vanishing theorem for the arithmetic right-hand side is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped Interval Topology

/-! ## GWSS-003A-1/2: named finite arithmetic surface -/

/-- The complete finite arithmetic right-hand side attached to a weight.

The top-horizontal contribution is deliberately a separate summand.  This
definition is only a finite-height abbreviation; it does not encode a limit
or a horizontal-decay assertion.
-/
noncomputable def pascalCenteredXiFiniteArithmeticRHS
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  2 * pascalXiOrdinaryZetaRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalXiArchimedeanRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalXiElementaryRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalCenteredXiTopHorizontalContribution h
      W.toContourTransportWindow

/-- The generic finite explicit formula expressed through the named RHS. -/
theorem pascalCenteredXiFiniteArithmeticRHS_eq_zeroMoment_factor
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiFiniteArithmeticRHS h W =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R := by
  unfold pascalCenteredXiFiniteArithmeticRHS
  exact (pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
    hh heven W).symm

/-- The corrected synthesized witness satisfies the same finite four-term
formula as any admissible even weight. -/
theorem pascalCenteredXiMellinWitnessFiniteExplicitFormula
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) W.R =
      2 * pascalXiOrdinaryZetaRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiArchimedeanRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.toContourTransportWindow := by
  exact pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
    (pascalCenteredXiMellinWitnessWeight_differentiable hε τ c)
    (pascalCenteredXiMellinWitnessWeight_even hε τ c) W

/-- The finite RHS phase forced by an off-critical actual zero.

The final equality is intentionally recorded as a consequence of the
zero-side detector identity.  It is not an independent arithmetic estimate
and must not be used as one in a source-rank argument.
-/
theorem exists_pascalCenteredXiMellinWitness_finiteArithmeticRHS_phase
    {z : ℂ} (W : PascalCenteredXiResidueTransportWindow)
    (hz : z ∈ pascalCenteredXiZeroDiskFinset W.R)
    (hre : z.re ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (z ^ 2).im ≠ 0 ∧
      ∃ τ : Fin (pascalCenteredXiSquaredOrbitIndexCard W.R) → ℝ,
        (∀ i, τ i ≠ 0) ∧ Function.Injective τ ∧
        ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard W.R) → ℂ,
          Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
          PascalCenteredEvenWeight
            (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
          pascalCenteredXiZeroDiskWeightedMoment
              (pascalCenteredXiMellinWitnessWeight ε τ c) W.R =
            ((z ^ 2).im : ℂ) * pascalCenteredXiSquaredOrbitMass W.R (z ^ 2) ∧
          pascalCenteredXiZeroDiskWeightedMoment
              (pascalCenteredXiMellinWitnessWeight ε τ c) W.R ≠ 0 ∧
          pascalCenteredXiFiniteArithmeticRHS
              (pascalCenteredXiMellinWitnessWeight ε τ c) W =
            -(2 * Real.pi * Complex.I) *
              (((z ^ 2).im : ℂ) *
                pascalCenteredXiSquaredOrbitMass W.R (z ^ 2)) := by
  obtain ⟨ε, hε, hqim, τ, hτ, hinj, c, hdiff, heven, hmoment, hne⟩ :=
    exists_pascalCenteredXiMellinOffCriticalWitness hz hre
  refine ⟨ε, hε, hqim, τ, hτ, hinj, c, hdiff, heven, hmoment, hne, ?_⟩
  rw [pascalCenteredXiFiniteArithmeticRHS_eq_zeroMoment_factor
    hdiff heven W, hmoment]

/-! ## GWSS-003A-3: pointwise finite-linearity bridges -/

/-- A witness multiplied by a fixed kernel is the corresponding finite sum of
the canonical Mellin weights multiplied by that kernel. -/
theorem pascalCenteredXiMellinWitnessWeight_mul_eq_sum
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (k : ℂ → ℂ) (z : ℂ) :
    pascalCenteredXiMellinWitnessWeight ε τ c z * k z =
      ∑ i, c i *
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) z * k z) := by
  unfold pascalCenteredXiMellinWitnessWeight
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Pointwise linearity of the ordinary-zeta right-edge integrand. -/
theorem pascalCenteredXiMellinWitnessOrdinaryZetaIntegrand_eq_sum
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (σ t : ℝ) :
    pascalXiOrdinaryZetaRightEdgeIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ c) σ t =
      ∑ i, c i * pascalXiOrdinaryZetaRightEdgeIntegrand
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) σ t := by
  unfold pascalXiOrdinaryZetaRightEdgeIntegrand
  have h := pascalCenteredXiMellinWitnessWeight_mul_eq_sum ε τ c
    (fun s => pascalXiOrdinaryZetaNegLogDeriv
      (pascalCenteredToOrdinary s) * Complex.I)
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))
  simpa [mul_assoc, pascalCenteredToOrdinary_pascalOrdinaryToCentered] using h

/-- Pointwise linearity of the finite prime/von Mangoldt cutoff integrand. -/
theorem pascalCenteredXiMellinWitnessPrimeCutoffIntegrand_eq_sum
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (σ : ℝ) (X : ℕ) (t : ℝ) :
    pascalPrimePowerRightEdgeCutoffIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ c) σ X t =
      ∑ i, c i * pascalPrimePowerRightEdgeCutoffIntegrand
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) σ X t := by
  unfold pascalPrimePowerRightEdgeCutoffIntegrand
  have h := pascalCenteredXiMellinWitnessWeight_mul_eq_sum ε τ c
    (fun s => pascalPrimePowerPHZFiniteUpTo X
      (pascalCenteredToOrdinary s) * Complex.I)
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))
  simpa [mul_assoc, pascalCenteredToOrdinary_pascalOrdinaryToCentered] using h

/-- Pointwise linearity of the archimedean correction integrand. -/
theorem pascalCenteredXiMellinWitnessArchimedeanIntegrand_eq_sum
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (σ t : ℝ) :
    pascalXiArchimedeanRightEdgeIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ c) σ t =
      ∑ i, c i * pascalXiArchimedeanRightEdgeIntegrand
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) σ t := by
  unfold pascalXiArchimedeanRightEdgeIntegrand
  have h := pascalCenteredXiMellinWitnessWeight_mul_eq_sum ε τ c
    (fun s => pascalXiArchimedeanLogDeriv
      (pascalCenteredToOrdinary s) * Complex.I)
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))
  simpa [mul_assoc, pascalCenteredToOrdinary_pascalOrdinaryToCentered] using h

/-- Pointwise linearity of the elementary correction integrand. -/
theorem pascalCenteredXiMellinWitnessElementaryIntegrand_eq_sum
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (σ t : ℝ) :
    pascalXiElementaryRightEdgeIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ c) σ t =
      ∑ i, c i * pascalXiElementaryRightEdgeIntegrand
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) σ t := by
  unfold pascalXiElementaryRightEdgeIntegrand
  have h := pascalCenteredXiMellinWitnessWeight_mul_eq_sum ε τ c
    (fun s => pascalXiElementaryLogDerivCorrection
      (pascalCenteredToOrdinary s) * Complex.I)
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))
  simpa [mul_assoc, pascalCenteredToOrdinary_pascalOrdinaryToCentered] using h

/-- Pointwise linearity of the fixed-Xi top-horizontal integrand. -/
theorem pascalCenteredXiMellinWitnessTopHorizontalIntegrand_eq_sum
    {n : ℕ} (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (T u : ℝ) :
    pascalCenteredXiTopHorizontalIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ c) T u =
      ∑ i, c i * pascalCenteredXiTopHorizontalIntegrand
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) T u := by
  unfold pascalCenteredXiTopHorizontalIntegrand
  have h := pascalCenteredXiMellinWitnessWeight_mul_eq_sum ε τ c
    pascalCenteredXiNegLogDeriv
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleTopEdge u T))
  exact h

end DkMath.RH.CFBRCProjection
