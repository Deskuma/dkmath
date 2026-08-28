/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaCofinalRadialDominationFrontierMinimizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaRadialMarginPrimeThresholdDecompositionAudit"

/-!
# CFZP-017: radial-margin prime-threshold decomposition

This module rewrites the finite radial margin as a prime contribution minus
an X-independent background threshold.  It also transports the CFZP-016
cofinal provider to a cofinal prime-threshold crossing interface.  The
threshold is not supplied, and phase-cell sign information is not promoted
to a threshold-crossing provider.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gate A: the normalized prime threshold -/

/-- The X-independent background threshold which the normalized prime
contribution must reach. -/
noncomputable def cfzp017NormalizedPrimeThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W -
    pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W -
    pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W

/-! ## Gate B: exact margin decomposition -/

/-- The finite radial margin is four pi times the normalized prime excess
over the fixed background threshold. -/
theorem cfzp017WholeShiftedRadialMargin_eq_four_pi_mul_primeThresholdExcess
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp015WholeShiftedRadialMargin ε W X =
      4 * Real.pi *
        (pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X -
          cfzp017NormalizedPrimeThreshold ε W) := by
  have hsurface :=
    pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_shiftedEnergyDifference
      hε W X
  have hscalar :=
    pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_pi_mul_normalizedArithmetic_re
      hε W X
  have hfour :=
    pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms
      hε W X
  unfold cfzp015WholeShiftedRadialMargin
  calc
    _ = 4 * (pascalCenteredXiMellinQuadraticScalarSurface ε W X -
        Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R) := by
      rw [← hsurface]
      ring
    _ = 4 * (Real.pi *
        ((pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re -
          pascalCenteredXiFixedRadialSecondMomentFunctional W.R)) := by
      rw [hscalar]
      ring
    _ = 4 * Real.pi *
        (pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X -
          cfzp017NormalizedPrimeThreshold ε W) := by
      rw [hfour]
      unfold cfzp017NormalizedPrimeThreshold
      ring

/-- Nonnegative radial margin is equivalent to crossing the normalized prime
threshold. -/
theorem cfzp017WholeShiftedRadialMargin_nonneg_iff_primeThreshold_le
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      cfzp017NormalizedPrimeThreshold ε W ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X := by
  rw [cfzp017WholeShiftedRadialMargin_eq_four_pi_mul_primeThresholdExcess hε W X]
  have hpi : 0 < (4 : ℝ) * Real.pi := by positivity
  constructor
  · intro h
    have hdiff : 0 ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X -
          cfzp017NormalizedPrimeThreshold ε W :=
      nonneg_of_mul_nonneg_right h hpi
    linarith
  · intro h
    exact mul_nonneg hpi.le (sub_nonneg.mpr h)

/-! ## Gate C: aggregate interaction and finite mode-sum companions -/

/-- The prime-threshold crossing can be expressed using the finite aggregate
interaction energy. -/
theorem cfzp017WholeShiftedRadialMargin_nonneg_iff_aggregateInteraction_ge
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      Real.pi * cfzp017NormalizedPrimeThreshold ε W ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  rw [cfzp017WholeShiftedRadialMargin_nonneg_iff_primeThreshold_le hε W X,
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateInteraction_div_pi
      hε W X]
  constructor
  · intro h
    have h' := (le_div_iff₀ Real.pi_pos).mp h
    simpa [mul_comm] using h'
  · intro h
    apply (le_div_iff₀ Real.pi_pos).mpr
    simpa [mul_comm] using h

/-- The prime-threshold crossing can also be expressed by the finite
von-Mangoldt mode sum. -/
theorem cfzp017WholeShiftedRadialMargin_nonneg_iff_modeSum_threshold
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      Real.pi * cfzp017NormalizedPrimeThreshold ε W ≤
        2 * (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeKernel ε W n) := by
  rw [cfzp017WholeShiftedRadialMargin_nonneg_iff_aggregateInteraction_ge hε W X,
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W X]

/-! ## Gate D: cofinal threshold crossing -/

/-- Cofinally many finite cutoffs cross the normalized prime threshold. -/
def Cfzp017CofinalPrimeThresholdCrossingAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ X : ℕ in atTop,
    cfzp017NormalizedPrimeThreshold ε W ≤
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X

/-- At fixed positive epsilon, cofinal radial domination and cofinal prime
threshold crossing are equivalent. -/
theorem cfzp017CofinalPrimeThresholdCrossingAt_iff_cfzp016
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp017CofinalPrimeThresholdCrossingAt ε W ↔
      Cfzp016CofinalCutoffRadialDominationAt ε W := by
  simp only [Cfzp017CofinalPrimeThresholdCrossingAt,
    Cfzp016CofinalCutoffRadialDominationAt]
  exact frequently_congr (Eventually.of_forall fun X =>
    (cfzp017WholeShiftedRadialMargin_nonneg_iff_primeThreshold_le hε W X).symm)

/-- Cofinal prime-threshold crossing occurs at cofinally many positive
smoothing parameters. -/
def Cfzp017DoublyCofinalPrimeThresholdCrossing
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ Cfzp017CofinalPrimeThresholdCrossingAt ε W

/-- The doubly cofinal prime-threshold crossing is exactly the CFZP-016
doubly cofinal radial-domination interface. -/
theorem cfzp017DoublyCofinalPrimeThresholdCrossing_iff_cfzp016
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp017DoublyCofinalPrimeThresholdCrossing W ↔
      Cfzp016DoublyCofinalRadialDomination W := by
  simp only [Cfzp017DoublyCofinalPrimeThresholdCrossing,
    Cfzp016DoublyCofinalRadialDomination]
  apply frequently_congr
  exact Eventually.of_forall fun ε => by
    constructor
    · rintro ⟨hε, hcross⟩
      exact ⟨hε, (cfzp017CofinalPrimeThresholdCrossingAt_iff_cfzp016 hε
        W).mp hcross⟩
    · rintro ⟨hε, hdom⟩
      exact ⟨hε, (cfzp017CofinalPrimeThresholdCrossingAt_iff_cfzp016 hε
        W).mpr hdom⟩

/-- The CFZP-016 finite-window criticality theorem can be restated using
doubly cofinal prime-threshold crossing. -/
theorem cfzp017FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdCrossing
    (W : PascalCenteredXiResidueTransportWindow)
    (hcross : Cfzp017DoublyCofinalPrimeThresholdCrossing W) :
    ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      ρ.re = (1 : ℝ) / 2 := by
  apply cfzp016FiniteWindowZeros_critical_of_doublyCofinalRadialDomination W
  exact (cfzp017DoublyCofinalPrimeThresholdCrossing_iff_cfzp016 W).mp hcross

/-! ## Gate E: sign-only versus threshold-crossing -/

/-- If the background threshold is nonpositive, prime nonnegativity is enough
to make the finite radial margin nonnegative. -/
theorem cfzp017WholeShiftedRadialMargin_nonneg_of_threshold_nonpos_of_prime_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hthreshold : cfzp017NormalizedPrimeThreshold ε W ≤ 0)
    (hprime : 0 ≤ pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X := by
  apply (cfzp017WholeShiftedRadialMargin_nonneg_iff_primeThreshold_le hε W X).mpr
  exact hthreshold.trans hprime

/-- Prime nonnegativity alone does not imply crossing of a positive
threshold; this is the real-number firewall for phase-cell reuse. -/
theorem cfzp017PrimeNonneg_does_not_imply_positiveThresholdCrossing :
    ∃ P T : ℝ, 0 ≤ P ∧ 0 < T ∧ ¬ T ≤ P := by
  refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-! ## Gate G: the sharpened provider frontier -/

/-- An independent doubly cofinal prime-threshold crossing provider remains
open. -/
inductive Cfzp017PrimeThresholdCrossingGap : Prop
  | noIndependentDoublyCofinalPrimeThresholdCrossingProvider

end DkMath.RH.CFBRCProjection
