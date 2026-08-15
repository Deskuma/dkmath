/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedBranchFreeRateAudit
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaFunctionalEquationReflection
import Mathlib.Tactic

/-!
# CS38: finite mirror-weighted source recovery

This module transports the CS37 rate ledger through the actual finite Mellin
weight and the oriented mirror half-interval.  It proves source identities and
normalisation consistency only.  No sign estimate, integral/limit exchange,
infinite Euler product, or RH conclusion is introduced.
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

/-! ## CS38-A: completed rate back to fixed-Xi coordinates -/

theorem pascalCenteredXiNegLogDeriv_eq_completedRate_add_elementary
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate s +
        pascalXiElementaryLogDerivCorrection s =
      pascalCenteredXiNegLogDeriv (pascalOrdinaryToCentered s) := by
  have hfixed := pascalCenteredXiNegLogDeriv_sub_center_eq_decomposed
    hs0 hs1 hzeta hGamma
  have hcompleted :=
    pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate_eq_ordinary_add_gamma
      hs0 hs1 hzeta hGamma
  unfold pascalXiDecomposedNegLogDeriv at hfixed
  rw [hcompleted]
  rw [← hfixed]

theorem pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate_eq_fixedXi_reflection
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0)
    (h1s0 : 1 - s ≠ 0) (h1s1 : 1 - s ≠ 1)
    (h1szeta : riemannZeta (1 - s) ≠ 0)
    (h1sGamma : Complex.Gammaℝ (1 - s) ≠ 0) :
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate s =
      2 * pascalCenteredXiNegLogDeriv
          (pascalOrdinaryToCentered s) -
        pascalXiElementaryLogDerivCorrection s +
        pascalXiElementaryLogDerivCorrection (1 - s) := by
  have hleft := pascalCenteredXiNegLogDeriv_eq_completedRate_add_elementary
    hs0 hs1 hzeta hGamma
  have hright := pascalCenteredXiNegLogDeriv_eq_completedRate_add_elementary
    h1s0 h1s1 h1szeta h1sGamma
  have hcenter : pascalOrdinaryToCentered (1 - s) =
      -pascalOrdinaryToCentered s := by
    simp [pascalOrdinaryToCentered, criticalLineCenter]
    ring
  have hCs : pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate s =
      pascalCenteredXiNegLogDeriv (pascalOrdinaryToCentered s) -
        pascalXiElementaryLogDerivCorrection s := by
    rw [← hleft]
    ring
  have hCref : pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate (1 - s) =
      pascalCenteredXiNegLogDeriv (pascalOrdinaryToCentered (1 - s)) -
        pascalXiElementaryLogDerivCorrection (1 - s) := by
    rw [← hright]
    ring
  unfold pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
  rw [hCs, hCref, hcenter, pascalCenteredXiNegLogDeriv_neg]
  ring

/-! ## CS38-B: weighted mirror channels -/

noncomputable def pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im

noncomputable def pascalCenteredXiPrimeSideFiniteGammaMirrorDensity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im

noncomputable def pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity
    (ε : ℝ) (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_eq_weighted_functionalEquation_channels
    {ε : ℝ}
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u =
      pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity ε W u +
        pascalCenteredXiPrimeSideFiniteGammaMirrorDensity ε W u +
        pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity ε X W u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity
    pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity
    pascalCenteredXiPrimeSideFiniteGammaMirrorDensity
    pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity
  rw [pascalCenteredXiPrimeSideFiniteResidualMirrorRate_eq_functionalEquationRate
    hSafe hu]
  simp only [pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate,
    mul_add, Complex.add_im]

/-! ## CS38-C: oriented half-interval recovery -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_mirror_weighted_half_integral
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
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (1 / Real.pi) *
        ∫ u in W.rectangle.σ..(1 / 2 : ℝ),
          pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u := by
  have hscalar := pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_residual_integral_im_div_two_pi
    hSafe hZeta hPHZ
  have hhalf := pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_integral_half_interval
    hε X hρ hρm hPairLeft hPairRight
  rw [hscalar]
  have him :
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))).im =
      ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W u := by
    simpa [pascalCenteredXiPrimeSideFiniteResidualScalarDensity,
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight,
      pascalCenteredXiPrimeSideFiniteResidualLogRate] using
      (intervalIntegral.intervalIntegral_im hWeighted).symm
  have htwo :
      (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))).im =
      2 * (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))).im := by
    simp
  rw [htwo, him, hhalf]
  field_simp [Real.pi_ne_zero]

/-! ## CS38-F/G: consistency frontier -/

inductive PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedRectangleReachGap : Prop
  | no_independent_rectangle_background_reach_provider

end DkMath.RH.CFBRCProjection
