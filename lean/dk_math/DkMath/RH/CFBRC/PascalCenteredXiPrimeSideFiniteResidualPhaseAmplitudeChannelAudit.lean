/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidualAudit
import Mathlib.Tactic

/-!
# CS31: finite residual phase/amplitude channels

This file records the next finite layer after CS30.  The finite prime-power
PHZ path is continuous, hence interval-integrable, and the residual
log-derivative is split into its real (amplitude) and imaginary (phase)
channels.  All identities below are finite identities on the top edge.

No logarithm branch, infinite Euler product, limit exchange, sign estimate,
or RH conclusion is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## CS31-A: finite PHZ regularity and automatic integrability -/

theorem pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_continuous
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Continuous
      (pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand ε W X) := by
  have hpath : Continuous (fun u : ℝ =>
      pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
    change Continuous (fun u : ℝ =>
      (u : ℂ) + (W.rectangle.T : ℂ) * Complex.I)
    fun_prop
  have hterm : ∀ n : ℕ, Continuous (fun u : ℝ =>
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hz : (fun u : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleTopEdge u W.rectangle.T) 0) =
          (fun _ : ℝ => 0) := by
        funext u
        rw [vonMangoldt_LSeries_term_eq]
        simp
      rw [hz]
      exact continuous_const
    · let : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
      have hnterm : (fun u : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleTopEdge u W.rectangle.T) n) =
          (fun u : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(pascalSymmetricRectangleTopEdge u W.rectangle.T)))) := by
        funext u
        rw [vonMangoldt_LSeries_term_eq]
      rw [hnterm]
      exact continuous_const.mul
        ((continuous_const_cpow (n : ℂ)).comp
          (continuous_neg.comp hpath))
  have hphz : Continuous (fun u : ℝ =>
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
    rw [show (fun u : ℝ => pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
      (fun u : ℝ => ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) n) by
      funext u
      exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _]
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  have hw := (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
    (ε := ε) (τ := 0) hε).continuous
  have hz : Continuous (fun u : ℝ =>
      pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
    change Continuous (fun u : ℝ =>
      ((u : ℂ) + (W.rectangle.T : ℂ) * Complex.I) - criticalLineCenter)
    fun_prop
  change Continuous ((fun u : ℝ =>
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))) *
    (fun u : ℝ => pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)))
  exact (hw.comp hz).mul hphz

theorem pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_intervalIntegrable
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand ε W X)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
  exact (pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_continuous
    hε W X).intervalIntegrable (μ := volume) W.rectangle.σ (1 - W.rectangle.σ)

theorem pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_two_residual_integral_of_finite_integrability
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X =
      2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
  exact pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_two_residual_integral
    hSafe hZeta
    (pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_intervalIntegrable
      hε W X)

/-! ## CS31-B: residual log-rate and the two exact channels -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualLogRate
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  -logDeriv (fun z : ℂ =>
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
    (pascalSymmetricRectangleTopEdge u W.rectangle.T)

noncomputable def pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).re

noncomputable def pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im

noncomputable def pascalCenteredXiPrimeSideFiniteResidualScalarDensity
    (ε : ℝ) (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
    pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im

noncomputable def pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity
    (ε : ℝ) (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))).re *
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u

noncomputable def pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity
    (ε : ℝ) (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))).im *
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u

theorem pascalCenteredXiPrimeSideFiniteResidualScalarDensity_eq_phase_add_amplitude
    (ε : ℝ) (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W u =
      pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W u +
        pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualScalarDensity
    pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate
  rw [Complex.mul_im]

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_phase_plus_amplitude_integrals
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hRate : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPhase : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hAmplitude : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W u) /
          Real.pi +
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W u) /
          Real.pi := by
  have hscalar :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_residual_integral_im_div_two_pi
      (hSafe := hSafe) (hZeta := hZeta)
      (hPHZ := pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_intervalIntegrable
        hε W X) (X := X)
  have hscalar' :
      pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
        (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im /
          (2 * Real.pi) := by
    simpa [pascalCenteredXiPrimeSideFiniteResidualLogRate] using hscalar
  rw [hscalar']
  have htwo : (2 * (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
      pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)).im =
      2 * (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im := by
    simp
  rw [htwo]
  have him :
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im =
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
            pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im := by
    exact (intervalIntegral.intervalIntegral_im hRate).symm
  rw [him]
  have hsplit :
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im) =
        (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W u) +
        (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W u) := by
    rw [← intervalIntegral.integral_add hPhase hAmplitude]
    apply intervalIntegral.integral_congr
    intro u hu
    exact pascalCenteredXiPrimeSideFiniteResidualScalarDensity_eq_phase_add_amplitude
      ε X W u
  rw [hsplit]
  field_simp [Real.pi_ne_zero]

/-! ## CS31-C: branch-free cumulative displacements -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  ∫ v in W.rectangle.σ..u,
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W v

noncomputable def pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  ∫ v in W.rectangle.σ..u,
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W v

@[simp] theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_basepoint
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W W.rectangle.σ = 0 := by
  simp [pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement]

@[simp] theorem pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_basepoint
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W W.rectangle.σ = 0 := by
  simp [pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement]

/-! ## CS31-D: channel-form reach and real countermodels -/

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonpos_iff_background_le_channel_integrals
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} (X : ℕ)
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hArch : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiArchimedeanLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hElem : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiElementaryLogDerivCorrection
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hRate : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPhase : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hAmplitude : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 ↔
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X ≤
        (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W u) /
            Real.pi +
        (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W u) /
            Real.pi := by
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonpos_iff_background_le_mismatch
    hε hSafe hZeta hArch hElem X]
  rw [pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_phase_plus_amplitude_integrals
    hε hSafe hZeta hRate hPhase hAmplitude]

theorem pascalCenteredXiPrimeSideFiniteResidual_channels_can_split_reach
    : ∃ B P A : ℝ, B ≤ P + A ∧ ¬ B ≤ P ∧ 0 ≤ A := by
  refine ⟨1, 0, 2, by norm_num, by norm_num, by norm_num⟩

theorem pascalCenteredXiPrimeSideFiniteResidual_channels_can_split_reach_symm
    : ∃ B P A : ℝ, B ≤ P + A ∧ 0 ≤ P ∧ ¬ B ≤ A := by
  refine ⟨1, 2, 0, by norm_num, by norm_num, by norm_num⟩

theorem pascalCenteredXiPrimeSideFiniteResidual_sum_lower_bound_need_not_control_either_channel
    : ∃ B P A : ℝ, B ≤ P + A ∧ ¬ 0 ≤ P ∧ ¬ 0 ≤ A := by
  refine ⟨-3, -1, -1, by norm_num, by norm_num, by norm_num⟩

/-! These are semantic boundaries, not missing algebraic proofs. -/

inductive PascalCenteredXiPrimeSideFiniteResidualChannelReachGap : Prop
  | no_independent_phase_amplitude_reach_estimate

inductive PascalCenteredXiPrimeSideFiniteResidualAmplitudeSemanticBridgeGap : Prop
  | no_log_abs_derivative_bridge

end DkMath.RH.CFBRCProjection
