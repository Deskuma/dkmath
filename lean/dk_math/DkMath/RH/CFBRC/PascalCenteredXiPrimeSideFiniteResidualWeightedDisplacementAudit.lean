/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualPolarTransportAudit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# CS33: finite residual endpoint and weighted displacement transport

This module closes the conditional finite transport layer after CS32.  The
phase endpoint formula is branch-free and the channel ledgers are finite
integration-by-parts identities.  The continuity of the residual rates is
kept as an explicit hypothesis: no continuity of `deriv riemannZeta` is
silently assumed.

No channel sign, reach estimate, infinite prime expansion, limit exchange, or
RH conclusion is asserted here.
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

/-! ## CS33-A/B: conditional displacement derivatives -/

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_hasDerivAt_of_continuous
    {W : PascalCenteredXiResidueTransportWindow}
    {X : ℕ}
    (hAmplitude : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W))
    {u : ℝ} :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W)
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u) u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement
  exact intervalIntegral.integral_hasDerivAt_right
    (hAmplitude.intervalIntegrable (μ := volume) W.rectangle.σ u)
    hAmplitude.aestronglyMeasurable.stronglyMeasurableAtFilter
    hAmplitude.continuousAt

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_hasDerivAt_of_continuous
    {W : PascalCenteredXiResidueTransportWindow}
    {X : ℕ}
    (hPhase : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W))
    {u : ℝ} :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W)
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u) u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement
  exact intervalIntegral.integral_hasDerivAt_right
    (hPhase.intervalIntegrable (μ := volume) W.rectangle.σ u)
    hPhase.aestronglyMeasurable.stronglyMeasurableAtFilter
    hPhase.continuousAt

/-! ## CS33-C: branch-free phase endpoint transport -/

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_eq_base_mul_exp_phaseDisplacement_of_continuous
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ}
    (hPhase : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W)) :
    pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W
        (1 - W.rectangle.σ) =
      pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W W.rectangle.σ *
        Complex.exp
          (-2 * Complex.I *
            (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
              (1 - W.rectangle.σ) : ℂ)) := by
  let U := pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W
  let Θ := pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
  let P := pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W
  let C : ℝ → ℂ := fun u => U u * Complex.exp (2 * Complex.I * (Θ u : ℂ))
  have hU : ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      HasDerivAt U
        (-2 * Complex.I * (P u) * U u) u := by
    intro u hu
    exact pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_hasDerivAt
      (X := X) hSafe hu
  have hΘ : ∀ u : ℝ, HasDerivAt Θ (P u) u := by
    intro u
    exact pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_hasDerivAt_of_continuous
      (X := X) hPhase
  have hC : ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      HasDerivAt C 0 u := by
    intro u hu
    have hExp : HasDerivAt (fun x : ℝ =>
        Complex.exp (2 * Complex.I * (Θ x : ℂ)))
        (2 * Complex.I * (P u : ℂ) *
          Complex.exp (2 * Complex.I * (Θ u : ℂ))) u := by
      have hThetaComplex : HasDerivAt (fun x : ℝ => (Θ x : ℂ))
          (P u : ℂ) u := (hΘ u).ofReal_comp
      have harg : HasDerivAt (fun x : ℝ =>
          2 * Complex.I * (Θ x : ℂ))
          (2 * Complex.I * (P u : ℂ)) u := by
        simpa [mul_assoc] using hThetaComplex.const_mul (2 * Complex.I)
      change HasDerivAt
        (Complex.exp ∘ fun x : ℝ => 2 * Complex.I * (Θ x : ℂ)) _ u
      simpa [mul_comm] using (Complex.hasDerivAt_exp _).comp u harg
    have hprod := (hU u hu).mul hExp
    apply hprod.congr_deriv
    ring
  have hconst := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hC u hu)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume
        W.rectangle.σ (1 - W.rectangle.σ))
  have hCequal : C (1 - W.rectangle.σ) = C W.rectangle.σ := by
    have hzero : (∫ _u in W.rectangle.σ..(1 - W.rectangle.σ), (0 : ℂ)) = 0 := by
      simp
    rw [hzero] at hconst
    exact sub_eq_zero.mp hconst.symm
  dsimp [C, U, Θ, P] at hCequal ⊢
  have hbase := pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_basepoint X W
  rw [hbase] at hCequal
  let q : ℂ := 2 * Complex.I *
    (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
      (1 - W.rectangle.σ) : ℂ)
  have hCequal' :
      pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W
          (1 - W.rectangle.σ) * Complex.exp q =
        pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W W.rectangle.σ := by
    simpa [q] using hCequal
  calc
    pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W
        (1 - W.rectangle.σ) =
        (pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W
          (1 - W.rectangle.σ) * Complex.exp q) * Complex.exp (-q) := by
      rw [mul_assoc, ← Complex.exp_add]
      simp
    _ = pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W W.rectangle.σ *
        Complex.exp (-q) := by rw [hCequal']
    _ = pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W W.rectangle.σ *
        Complex.exp
          (-2 * Complex.I *
            (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
              (1 - W.rectangle.σ) : ℂ)) := by
      congr 2
      dsimp [q]
      ring

/-! ## CS33-E: finite Mellin weight channels -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleTopEdge u W.rectangle.T))

noncomputable def pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u).re

noncomputable def pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u).im

noncomputable def pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  deriv (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalOrdinaryToCentered
      (pascalSymmetricRectangleTopEdge u W.rectangle.T))

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_hasDerivAt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {u : ℝ} :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W)
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u) u := by
  have hpath : HasDerivAt
      (fun v : ℝ => pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge v W.rectangle.T)) (1 : ℂ) u := by
    change HasDerivAt (fun v : ℝ =>
      ((v : ℂ) + (W.rectangle.T : ℂ) * Complex.I) - criticalLineCenter) 1 u
    simpa using (((hasDerivAt_id (u : ℂ)).comp_ofReal).add_const
      ((W.rectangle.T : ℂ) * Complex.I)).sub_const criticalLineCenter
  have hw := (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
    (ε := ε) (τ := 0) hε
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))).hasDerivAt
  have hcomp := hw.comp u hpath
  change HasDerivAt
    (fun v : ℝ => pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W v) _ u
  simpa [Function.comp_def,
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight,
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative] using hcomp

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_hasDerivAt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {u : ℝ} :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W)
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re u := by
  have h := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_hasDerivAt
    (u := u) hε W
  unfold pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal
  change HasDerivAt
    (fun v : ℝ =>
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W v).re) _ u
  simpa [Function.comp_def, Complex.reCLM_apply] using
    ((Complex.reCLM.hasFDerivAt.comp u h.hasFDerivAt).hasDerivAt)

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_hasDerivAt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {u : ℝ} :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W)
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im u := by
  have h := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_hasDerivAt
    (u := u) hε W
  unfold pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag
  change HasDerivAt
    (fun v : ℝ =>
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W v).im) _ u
  simpa [Function.comp_def, Complex.imCLM_apply] using
    ((Complex.imCLM.hasFDerivAt.comp u h.hasFDerivAt).hasDerivAt)

/-! ## CS33-F/G/H: generic finite weighted displacement ledger -/

theorem pascalCenteredXiPrimeSideFiniteResidual_weighted_displacement_ledger
    {a b : ℝ} {w w' v v' : ℝ → ℝ} {D : ℝ → ℝ}
    (hw : ∀ u ∈ Set.uIcc a b, HasDerivAt w (w' u) u)
    (hv : ∀ u ∈ Set.uIcc a b, HasDerivAt v (v' u) u)
    (hw' : IntervalIntegrable w' volume a b)
    (hv' : IntervalIntegrable v' volume a b)
    (hD : ∀ u, v u = D u) :
    (∫ u in a..b, w u * v' u) =
      w b * D b - w a * D a - ∫ u in a..b, w' u * D u := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun u hu => (hw u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hv u hu).continuousAt.continuousWithinAt)
    (fun u hu => hw u (mem_Icc_of_Ioo hu))
    (fun u hu => hv u (mem_Icc_of_Ioo hu))
    hw' hv'
  simpa [hD] using h

theorem pascalCenteredXiPrimeSideFiniteResidual_phase_channel_displacement_ledger
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    {wP wP' : ℝ → ℝ}
    (hwP : ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      HasDerivAt wP (wP' u) u)
    (hP : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W))
    (hwP' : IntervalIntegrable wP' volume W.rectangle.σ (1 - W.rectangle.σ)) :
    (∫ u in W.rectangle.σ..(1 - W.rectangle.σ), wP u *
      pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u) =
      wP (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
            (1 - W.rectangle.σ) -
        wP W.rectangle.σ *
          pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
            W.rectangle.σ -
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          wP' u * pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u := by
  apply pascalCenteredXiPrimeSideFiniteResidual_weighted_displacement_ledger
    (v := pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W)
    (v' := pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W)
    (D := pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W) hwP
  · intro u hu
    exact pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_hasDerivAt_of_continuous
      (X := X) hP (u := u)
  · exact hwP'
  · exact hP.intervalIntegrable (μ := volume) W.rectangle.σ (1 - W.rectangle.σ)
  · intro u
    rfl

theorem pascalCenteredXiPrimeSideFiniteResidual_amplitude_channel_displacement_ledger
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    {wA wA' : ℝ → ℝ}
    (hwA : ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      HasDerivAt wA (wA' u) u)
    (hA : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W))
    (hwA' : IntervalIntegrable wA' volume W.rectangle.σ (1 - W.rectangle.σ)) :
    (∫ u in W.rectangle.σ..(1 - W.rectangle.σ), wA u *
      pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u) =
      wA (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
            (1 - W.rectangle.σ) -
        wA W.rectangle.σ *
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
            W.rectangle.σ -
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          wA' u * pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u := by
  apply pascalCenteredXiPrimeSideFiniteResidual_weighted_displacement_ledger
    (v := pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W)
    (v' := pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
    (D := pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W) hwA
  · intro u hu
    exact pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_hasDerivAt_of_continuous
      (X := X) hA (u := u)
  · exact hwA'
  · exact hA.intervalIntegrable (μ := volume) W.rectangle.σ (1 - W.rectangle.σ)
  · intro u
    rfl

/-! The two channel ledgers with the actual finite Mellin weight.  The
    derivative integrability hypotheses are deliberately explicit: they are
    the only remaining finite regularity input for the weight-variation
    remainder. -/

theorem pascalCenteredXiPrimeSideFiniteResidual_top_phase_channel_displacement_ledger
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hP : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W))
    (hWeight' : IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W u *
        pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u) =
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W
          (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
            (1 - W.rectangle.σ) -
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re *
            pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u := by
  have h := pascalCenteredXiPrimeSideFiniteResidual_phase_channel_displacement_ledger
    (W := W) (X := X)
    (wP := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W)
    (wP' := fun u =>
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re)
    (fun u hu => pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_hasDerivAt
      hε W (u := u)) hP hWeight'
  simpa [pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_basepoint] using h

theorem pascalCenteredXiPrimeSideFiniteResidual_top_amplitude_channel_displacement_ledger
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hA : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W))
    (hWeight' : IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W u *
        pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u) =
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W
          (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
            (1 - W.rectangle.σ) -
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im *
            pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u := by
  have h := pascalCenteredXiPrimeSideFiniteResidual_amplitude_channel_displacement_ledger
    (W := W) (X := X)
    (wA := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W)
    (wA' := fun u =>
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im)
    (fun u hu => pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_hasDerivAt
      hε W (u := u)) hA hWeight'
  simpa [pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_basepoint] using h

/-! ## CS33-H: exact scalar mismatch displacement ledger -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_weighted_displacement_ledger
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
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hP : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W))
    (hA : Continuous
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W))
    (hWeightRe' : IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeightIm' : IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W
          (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
            (1 - W.rectangle.σ) +
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W
          (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
            (1 - W.rectangle.σ) -
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          ((pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re *
              pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u +
            (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im *
              pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u)) /
        Real.pi := by
  have hMismatch :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_phase_plus_amplitude_integrals
      hε hSafe hZeta hRate hPhase hAmplitude
  have hPhaseLedger :=
    pascalCenteredXiPrimeSideFiniteResidual_top_phase_channel_displacement_ledger
      hε hP hWeightRe'
  have hAmplitudeLedger :=
    pascalCenteredXiPrimeSideFiniteResidual_top_amplitude_channel_displacement_ledger
      hε hA hWeightIm'
  have hPhaseIntegral :
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W u) =
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W u *
            pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rfl
  have hAmplitudeIntegral :
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W u) =
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W u *
            pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rfl
  have hThetaCont : ContinuousOn
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
    intro u hu
    exact (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_hasDerivAt_of_continuous
      (X := X) hP (u := u)).continuousAt.continuousWithinAt
  have hDCont : ContinuousOn
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
    intro u hu
    exact (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_hasDerivAt_of_continuous
      (X := X) hA (u := u)).continuousAt.continuousWithinAt
  have hRem :
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re *
              pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u +
            (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im *
              pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u) =
        (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re *
            pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u) +
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im *
            pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u := by
    rw [intervalIntegral.integral_add
      (hWeightRe'.mul_continuousOn hThetaCont)
      (hWeightIm'.mul_continuousOn hDCont)]
  rw [hMismatch, hPhaseIntegral, hAmplitudeIntegral,
    hPhaseLedger, hAmplitudeLedger]
  rw [hRem]
  ring

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_weighted_displacement_log_normSq_endpoint_of_ledger
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hLedger :
      pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W
            (1 - W.rectangle.σ) *
            pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
              (1 - W.rectangle.σ) +
          pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W
            (1 - W.rectangle.σ) *
            pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
              (1 - W.rectangle.σ) -
          ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
            ((pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re *
                pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u +
              (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im *
                pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u)) /
          Real.pi)
    (hAmplitude : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W
          (1 - W.rectangle.σ) *
          pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W
            (1 - W.rectangle.σ) +
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W
          (1 - W.rectangle.σ) *
          ((Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
              W.rectangle.σ) -
            Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
              (1 - W.rectangle.σ))) / 2) -
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          ((pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re *
              pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W u +
            (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im *
              pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W u)) /
        Real.pi := by
  have hEndpoint :=
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_eq_log_normSq_endpoint
      (X := X) hSafe hAmplitude
  rw [hLedger, hEndpoint]

/-! Bonus: the real endpoint transport can be read multiplicatively.  This
    is still an ordinary positive-real identity; it does not choose a square
    root or a complex logarithm. -/

theorem pascalCenteredXiPrimeSideFiniteResidualNormSq_endpoint_eq_base_mul_exp_neg_two_amplitudeDisplacement
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ}
    (hAmplitude : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualNormSq X W (1 - W.rectangle.σ) =
      pascalCenteredXiPrimeSideFiniteResidualNormSq X W W.rectangle.σ *
        Real.exp (-2 *
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
            (1 - W.rectangle.σ)) := by
  have hEndpoint :=
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_eq_log_normSq_endpoint
      (X := X) hSafe hAmplitude
  have hσ' : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have huBase : W.rectangle.σ ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) := by
    rw [Set.uIcc_of_ge hσ']
    exact ⟨by linarith, le_rfl⟩
  have huTop : 1 - W.rectangle.σ ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) := by
    rw [Set.uIcc_of_ge hσ']
    exact ⟨le_rfl, by linarith⟩
  have hbase := pascalCenteredXiPrimeSideFiniteResidualNormSq_pos
    (X := X) hSafe huBase
  have htop := pascalCenteredXiPrimeSideFiniteResidualNormSq_pos
    (X := X) hSafe huTop
  rw [hEndpoint]
  have harg : -2 *
      ((Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W W.rectangle.σ) -
        Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          (1 - W.rectangle.σ))) / 2) =
      Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          (1 - W.rectangle.σ)) -
        Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W W.rectangle.σ) := by
    ring
  rw [harg, Real.exp_sub, Real.exp_log htop, Real.exp_log hbase]
  field_simp [ne_of_gt hbase]

/-! ## CS33-I/firewall frontier -/

inductive PascalCenteredXiPrimeSideFiniteResidualWeightedDisplacementReachGap : Prop
  | no_independent_weighted_displacement_reach_estimate

inductive PascalCenteredXiPrimeSideFiniteResidualRateContinuityGap : Prop
  | no_source_derived_continuity_of_deriv_riemannZeta_supplied

end DkMath.RH.CFBRCProjection
