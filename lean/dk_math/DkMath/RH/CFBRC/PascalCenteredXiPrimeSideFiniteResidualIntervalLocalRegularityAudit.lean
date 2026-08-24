/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualWeightedDisplacementAudit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# CS34: interval-local residual regularity

This module removes the global continuity certificates from CS33.  The
ordinary zeta log derivative, the finite prime-power PHZ path, and the Euler
renormalized residual are treated only on the safe finite top interval.  The
construction does not assert a zero-free strip or any limiting prime-side
statement.
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

/-! ## CS34-A/B: local source regularity -/

private theorem pascalCenteredXiPrimeSideFiniteResidual_topPath_continuous
    (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (fun u : ℝ =>
      pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  change Continuous (fun u : ℝ =>
    (u : ℂ) + (W.rectangle.T : ℂ) * Complex.I)
  fun_prop

theorem pascalCenteredXiPrimeSideFiniteResidualOrdinaryZetaNegLogDeriv_continuousAt_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {u : ℝ} (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    ContinuousAt
      (fun v : ℝ => pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleTopEdge v W.rectangle.T)) u := by
  dsimp [IsPascalCenteredXiTopLogDerivDecompositionSafe] at hSafe
  have hs := hSafe u hu
  have hzAnalytic : AnalyticAt ℂ riemannZeta
      (pascalSymmetricRectangleTopEdge u W.rectangle.T) :=
    analyticOn_riemannZeta _ (by simpa using hs.2.1)
  have hordinary : ContinuousAt pascalXiOrdinaryZetaNegLogDeriv
      (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
    change ContinuousAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z)
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)
    exact (hzAnalytic.deriv.continuousAt.neg).div hzAnalytic.continuousAt hs.2.2.1
  have hpath : ContinuousAt
      (fun v : ℝ => pascalSymmetricRectangleTopEdge v W.rectangle.T) u := by
    exact (pascalCenteredXiPrimeSideFiniteResidual_topPath_continuous W).continuousAt
  simpa [Function.comp_def] using
    (ContinuousAt.comp (f := fun v : ℝ =>
      pascalSymmetricRectangleTopEdge v W.rectangle.T)
      (g := pascalXiOrdinaryZetaNegLogDeriv) hordinary hpath)

private theorem pascalCenteredXiPrimeSideFinitePHZ_top_continuous
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Continuous (fun u : ℝ => pascalPrimePowerPHZFiniteUpTo X
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
  by_cases hn0 : n = 0
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
  · let : NeZero (n : ℂ) := ⟨by exact_mod_cast hn0⟩
    have hnterm : (fun u : ℝ =>
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) n) =
      (fun u : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((n : ℂ) ^ (-(pascalSymmetricRectangleTopEdge u W.rectangle.T)))) := by
      funext u
      rw [vonMangoldt_LSeries_term_eq]
    rw [hnterm]
    have hpath := pascalCenteredXiPrimeSideFiniteResidual_topPath_continuous
      (W := W)
    exact continuous_const.mul
      ((continuous_const_cpow (n : ℂ)).comp (continuous_neg.comp hpath))

theorem pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousAt_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    ContinuousAt
      (pascalCenteredXiPrimeSideFiniteResidualLogRate X W) u := by
  let path : ℝ → ℂ := fun v => pascalSymmetricRectangleTopEdge v W.rectangle.T
  have hpath : Continuous path := by
    exact pascalCenteredXiPrimeSideFiniteResidual_topPath_continuous (W := W)
  have hlocalOrd :=
    pascalCenteredXiPrimeSideFiniteResidualOrdinaryZetaNegLogDeriv_continuousAt_of_safe
      hSafe hu
  have hOrd : ContinuousAt (fun v : ℝ => pascalXiOrdinaryZetaNegLogDeriv (path v)) u := by
    simpa [path] using hlocalOrd
  have hPhz : ContinuousAt (fun v : ℝ => pascalPrimePowerPHZFiniteUpTo X (path v)) u := by
    exact (pascalCenteredXiPrimeSideFinitePHZ_top_continuous W X).continuousAt
  have hs := hSafe u hu
  have hEq : ∀ᶠ v in 𝓝 u,
      pascalCenteredXiPrimeSideFiniteResidualLogRate X W v =
        pascalXiOrdinaryZetaNegLogDeriv (path v) -
          pascalPrimePowerPHZFiniteUpTo X (path v) := by
    have hpath' : ContinuousAt path u := hpath.continuousAt
    have hzpath : ContinuousAt (fun v : ℝ => riemannZeta (path v)) u :=
      (analyticOn_riemannZeta (path u) (by simpa [path] using hs.2.1)).continuousAt.comp
        hpath'
    have hne1 : {v : ℝ | path v ≠ 1} ∈ 𝓝 u := by
      exact hpath'.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hs.2.1)
    have hne0 : {v : ℝ | riemannZeta (path v) ≠ 0} ∈ 𝓝 u := by
      exact hzpath.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hs.2.2.1)
    filter_upwards [hne1, hne0] with v hv1 hv0
    simpa [pascalCenteredXiPrimeSideFiniteResidualLogRate, path] using
      pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
        (X := X) hv1 hv0
  have hRhs : ContinuousAt
      (fun v : ℝ => pascalXiOrdinaryZetaNegLogDeriv (path v) -
        pascalPrimePowerPHZFiniteUpTo X (path v)) u := hOrd.sub hPhz
  have hres := hRhs.congr_of_eventuallyEq hEq
  simpa [path] using hres

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousAt_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    ContinuousAt (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W) u := by
  change ContinuousAt (fun u : ℝ =>
    (pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).re) u
  exact Complex.continuous_re.continuousAt.comp
    (pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousAt_of_safe hSafe hu)

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousAt_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    ContinuousAt (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W) u := by
  change ContinuousAt (fun u : ℝ =>
    (pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im) u
  exact Complex.continuous_im.continuousAt.comp
    (pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousAt_of_safe hSafe hu)

theorem pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualLogRate X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  intro u hu
  exact (pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousAt_of_safe hSafe hu).continuousWithinAt

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousOn_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  intro u hu
  exact (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousAt_of_safe
    hSafe hu).continuousWithinAt

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousOn_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  intro u hu
  exact (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousAt_of_safe
    hSafe hu).continuousWithinAt

theorem pascalCenteredXiPrimeSideFiniteResidualLogRate_intervalIntegrable_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    IntervalIntegrable (pascalCenteredXiPrimeSideFiniteResidualLogRate X W)
      volume W.rectangle.σ (1 - W.rectangle.σ) :=
  (pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe hSafe X).intervalIntegrable

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    IntervalIntegrable (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
      volume W.rectangle.σ (1 - W.rectangle.σ) :=
  (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousOn_of_safe hSafe X).intervalIntegrable

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    IntervalIntegrable (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W)
      volume W.rectangle.σ (1 - W.rectangle.σ) :=
  (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousOn_of_safe hSafe X).intervalIntegrable

private theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_continuousOn
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  have hw := (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
    (ε := ε) (τ := 0) hε).continuous
  have hpath : Continuous (fun u : ℝ =>
      pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
    change Continuous (fun u : ℝ =>
      (u : ℂ) + (W.rectangle.T : ℂ) * Complex.I - criticalLineCenter)
    fun_prop
  exact (hw.comp hpath).continuousOn

private theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_continuousOn
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  have hcont := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_continuousOn hε W
  exact Complex.continuous_re.continuousOn.comp hcont (fun _ _ => Set.mem_univ _)

private theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_continuousOn
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  have hcont := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_continuousOn hε W
  exact Complex.continuous_im.continuousOn.comp hcont (fun _ _ => Set.mem_univ _)

/-! A local version of the finite product rule.  The derivative hypotheses are
    needed only on the open interval; the endpoint values are supplied by the
    continuous-on hypotheses. -/

theorem pascalCenteredXiPrimeSideFiniteResidual_weighted_displacement_ledger_of_interval_local
    {a b : ℝ} {w w' v v' : ℝ → ℝ}
    (hw : ContinuousOn w (Set.uIcc a b))
    (hv : ContinuousOn v (Set.uIcc a b))
    (hw' : ∀ u ∈ Set.Ioo (min a b) (max a b), HasDerivAt w (w' u) u)
    (hv' : ∀ u ∈ Set.Ioo (min a b) (max a b), HasDerivAt v (v' u) u)
    (hwInt : IntervalIntegrable w' volume a b)
    (hvInt : IntervalIntegrable v' volume a b) :
    (∫ u in a..b, w u * v' u) =
      w b * v b - w a * v a - ∫ u in a..b, w' u * v u := by
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hw hv hw' hv' hwInt hvInt

private theorem phase_displacement_hasDerivAt_of_safe_interior
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) {X : ℕ}
    {u : ℝ} (hu : u ∈ Set.Ioo (min W.rectangle.σ (1 - W.rectangle.σ))
      (max W.rectangle.σ (1 - W.rectangle.σ))) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W)
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u) u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement
  have hInt := pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe
    hSafe X
  have hInt' := hInt.mono_set
    (uIcc_subset_uIcc_left (mem_Icc_of_Ioo hu))
  have hmeas : StronglyMeasurableAtFilter
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W) (𝓝 u) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo
      (fun v hv => pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousAt_of_safe
        (X := X) hSafe (mem_Icc_of_Ioo hv)) u hu
  exact intervalIntegral.integral_hasDerivAt_right hInt' hmeas
    (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousAt_of_safe
      (X := X) hSafe (mem_Icc_of_Ioo hu))

/-! ## CS34-C/F: source-derived branch-free phase transport -/

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_eq_base_mul_exp_phaseDisplacement_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
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
  let S := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
  let C : ℝ → ℂ := fun u => U u * Complex.exp (2 * Complex.I * (Θ u : ℂ))
  have hPInt : IntervalIntegrable P volume W.rectangle.σ (1 - W.rectangle.σ) :=
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe hSafe X
  have hPCont : ContinuousOn P S :=
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousOn_of_safe hSafe X
  have hThetaCont : ContinuousOn Θ S := by
    exact intervalIntegral.continuousOn_primitive_interval'
      hPInt (left_mem_uIcc : W.rectangle.σ ∈ S)
  have hU : ∀ u ∈ S, HasDerivAt U
      (-2 * Complex.I * (P u) * U u) u := by
    intro u hu
    exact pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_hasDerivAt
      (X := X) hSafe hu
  have hUCont : ContinuousOn U S := fun u hu =>
    (hU u hu).continuousAt.continuousWithinAt
  have hThetaComplex : ContinuousOn (fun u : ℝ => (Θ u : ℂ)) S :=
    Complex.continuous_ofReal.continuousOn.comp hThetaCont (fun _ _ => Set.mem_univ _)
  have hArgCont : ContinuousOn (fun u : ℝ => 2 * Complex.I * (Θ u : ℂ)) S :=
    hThetaComplex.const_mul (2 * Complex.I)
  have hExpCont : ContinuousOn (fun u : ℝ =>
      Complex.exp (2 * Complex.I * (Θ u : ℂ))) S := by
    simpa [Function.comp_def] using
      Complex.continuous_exp.continuousOn.comp hArgCont (fun _ _ => Set.mem_univ _)
  have hCCont : ContinuousOn C S := by
    exact hUCont.mul hExpCont
  have hab : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have hCderiv : ∀ u ∈ Set.Ioo (1 - W.rectangle.σ) W.rectangle.σ,
      HasDerivAt C 0 u := by
    intro u hu
    have huS : u ∈ S := by
      simpa [S, hab] using (mem_Icc_of_Ioo hu)
    have hTheta : HasDerivAt Θ (P u) u :=
      phase_displacement_hasDerivAt_of_safe_interior hSafe (by simpa [hab] using hu)
    have hExp : HasDerivAt (fun x : ℝ =>
        Complex.exp (2 * Complex.I * (Θ x : ℂ)))
        (2 * Complex.I * (P u : ℂ) *
          Complex.exp (2 * Complex.I * (Θ u : ℂ))) u := by
      have hThetaComplex' : HasDerivAt (fun x : ℝ => (Θ x : ℂ))
          (P u : ℂ) u := hTheta.ofReal_comp
      have harg : HasDerivAt (fun x : ℝ =>
          2 * Complex.I * (Θ x : ℂ))
          (2 * Complex.I * (P u : ℂ)) u := by
        simpa [mul_assoc] using hThetaComplex'.const_mul (2 * Complex.I)
      change HasDerivAt
        (Complex.exp ∘ fun x : ℝ => 2 * Complex.I * (Θ x : ℂ)) _ u
      simpa [mul_comm] using (Complex.hasDerivAt_exp _).comp u harg
    have hprod := (hU u huS).mul hExp
    apply hprod.congr_deriv
    ring
  have hconst := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := 1 - W.rectangle.σ) (b := W.rectangle.σ) hab
    (hCCont.mono (by
      change Set.Icc (1 - W.rectangle.σ) W.rectangle.σ ⊆
        Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
      rw [Set.uIcc_of_ge hab])) hCderiv
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume
        (1 - W.rectangle.σ) W.rectangle.σ)
  have hCequal : C (1 - W.rectangle.σ) = C W.rectangle.σ := by
    have hzero : (∫ _u in (1 - W.rectangle.σ)..W.rectangle.σ, (0 : ℂ)) = 0 := by
      simp
    rw [hzero] at hconst
    exact (sub_eq_zero.mp hconst.symm).symm
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

/-! ## CS34-D: source-derived Mellin derivative regularity -/

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_continuousAt
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) {u : ℝ} :
    ContinuousAt
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W) u := by
  let path : ℝ → ℂ := fun v => pascalOrdinaryToCentered
    (pascalSymmetricRectangleTopEdge v W.rectangle.T)
  have hpath : ContinuousAt path u := by
    change ContinuousAt (fun v : ℝ =>
      (v : ℂ) + (W.rectangle.T : ℂ) * Complex.I - criticalLineCenter) u
    fun_prop
  have hw : Differentiable ℂ
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0) :=
    pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε
  have hderiv : ContinuousAt (deriv
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)) (path u) :=
    (hw.analyticAt (path u)).deriv.continuousAt
  change ContinuousAt
    (deriv (pascalCenteredXiMellinSecondDifferenceWeight ε 0) ∘ path) u
  exact ContinuousAt.comp (f := path)
    (g := deriv (pascalCenteredXiMellinSecondDifferenceWeight ε 0)) hderiv hpath

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_continuousOn
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  intro u hu
  exact (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_continuousAt
    hε W).continuousWithinAt

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_intervalIntegrable
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W)
      volume W.rectangle.σ (1 - W.rectangle.σ) :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_continuousOn
    hε W).intervalIntegrable

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivativeReal_intervalIntegrable
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
  have hcont := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_continuousOn
    hε W
  have hre : ContinuousOn
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :=
    Complex.continuous_re.continuousOn.comp (s := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ))
      (t := Set.univ) hcont (fun _ _ => Set.mem_univ _)
  exact hre.intervalIntegrable

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivativeImag_intervalIntegrable
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
  have hcont := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative_continuousOn
    hε W
  have him : ContinuousOn
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :=
    Complex.continuous_im.continuousOn.comp (s := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ))
      (t := Set.univ) hcont (fun _ _ => Set.mem_univ _)
  exact him.intervalIntegrable

/-! ## CS34-C/E: local gauge and automatic finite input ledgers -/

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_hasDerivAt_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) {X : ℕ}
    {u : ℝ} (hu : u ∈ Set.Ioo (min W.rectangle.σ (1 - W.rectangle.σ))
      (max W.rectangle.σ (1 - W.rectangle.σ))) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W)
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u) u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement
  have hInt := pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
    hSafe X
  have hInt' := hInt.mono_set
    (uIcc_subset_uIcc_left (mem_Icc_of_Ioo hu))
  have hmeas : StronglyMeasurableAtFilter
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W) (𝓝 u) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo
      (fun v hv => pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousAt_of_safe
        (X := X) hSafe (mem_Icc_of_Ioo hv)) u hu
  exact intervalIntegral.integral_hasDerivAt_right hInt' hmeas
    (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousAt_of_safe
      hSafe (mem_Icc_of_Ioo hu))

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_hasDerivAt_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) {X : ℕ}
    {u : ℝ} (hu : u ∈ Set.Ioo (min W.rectangle.σ (1 - W.rectangle.σ))
      (max W.rectangle.σ (1 - W.rectangle.σ))) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W)
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u) u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement
  have hInt := pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe
    hSafe X
  have hInt' := hInt.mono_set
    (uIcc_subset_uIcc_left (mem_Icc_of_Ioo hu))
  have hmeas : StronglyMeasurableAtFilter
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W) (𝓝 u) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo
      (fun v hv => pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousAt_of_safe
        (X := X) hSafe (mem_Icc_of_Ioo hv)) u hu
  exact intervalIntegral.integral_hasDerivAt_right hInt' hmeas
    (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousAt_of_safe
      hSafe (mem_Icc_of_Ioo hu))

/-! ## CS34-G: source-derived channel ledgers -/

theorem pascalCenteredXiPrimeSideFiniteResidual_top_phase_channel_displacement_ledger_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) :
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
  let S := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
  have hW := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_continuousOn hε W
  have hTheta : ContinuousOn
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W) S := by
    exact intervalIntegral.continuousOn_primitive_interval'
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe
        hSafe X) (left_mem_uIcc : W.rectangle.σ ∈ S)
  have hW' : IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).re)
      volume W.rectangle.σ (1 - W.rectangle.σ) :=
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivativeReal_intervalIntegrable
      hε W
  have h := pascalCenteredXiPrimeSideFiniteResidual_weighted_displacement_ledger_of_interval_local
    (a := W.rectangle.σ) (b := 1 - W.rectangle.σ)
    hW hTheta
    (fun u hu => pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_hasDerivAt
      hε W (u := u))
    (fun u hu => phase_displacement_hasDerivAt_of_safe_interior hSafe
      (X := X) hu)
    hW'
    (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe
      hSafe X)
  simpa [S, pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement_basepoint] using h

theorem pascalCenteredXiPrimeSideFiniteResidual_top_amplitude_channel_displacement_ledger_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) :
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
  let S := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
  have hW := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_continuousOn hε W
  have hD : ContinuousOn
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W) S := by
    exact intervalIntegral.continuousOn_primitive_interval'
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
        hSafe X) (left_mem_uIcc : W.rectangle.σ ∈ S)
  have hW' : IntervalIntegrable
      (fun u : ℝ =>
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivative ε W u).im)
      volume W.rectangle.σ (1 - W.rectangle.σ) :=
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivativeImag_intervalIntegrable
      hε W
  have h := pascalCenteredXiPrimeSideFiniteResidual_weighted_displacement_ledger_of_interval_local
    (a := W.rectangle.σ) (b := 1 - W.rectangle.σ)
    hW hD
    (fun u hu => pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_hasDerivAt
      hε W (u := u))
    (fun u hu => pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_hasDerivAt_of_safe
      hSafe (X := X) hu)
    hW'
    (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
      hSafe X)
  simpa [S, pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_basepoint] using h

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_weighted_displacement_ledger_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) :
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
  let S := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
  have hWeight := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_continuousOn hε W
  have hOrd : ContinuousOn
      (fun u : ℝ => pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) S := by
    intro u hu
    exact (pascalCenteredXiPrimeSideFiniteResidualOrdinaryZetaNegLogDeriv_continuousAt_of_safe
      hSafe hu).continuousWithinAt
  have hResidual := pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe
    hSafe X
  have hZetaInt : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
    have hc : ContinuousOn
        (fun u : ℝ =>
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalXiOrdinaryZetaNegLogDeriv
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) S := by
      change ContinuousOn
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W *
          (fun u : ℝ => pascalXiOrdinaryZetaNegLogDeriv
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))) S
      exact hWeight.mul hOrd
    exact hc.intervalIntegrable
  have hRateInt : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
    have hc : ContinuousOn
        (fun u : ℝ =>
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u) S := by
      change ContinuousOn
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W) S
      exact hWeight.mul hResidual
    exact hc.intervalIntegrable
  have hPhaseInt : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
    have hWRe := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_continuousOn
      hε W
    have hP := pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_continuousOn_of_safe
      hSafe X
    have hc : ContinuousOn
        (pascalCenteredXiPrimeSideFiniteResidualPhaseChannelDensity ε X W) S := by
      change ContinuousOn
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W *
          pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W) S
      exact hWRe.mul hP
    exact hc.intervalIntegrable
  have hAmplitudeInt : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
    have hWIm := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_continuousOn
      hε W
    have hA := pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_continuousOn_of_safe
      hSafe X
    have hc : ContinuousOn
        (pascalCenteredXiPrimeSideFiniteResidualAmplitudeChannelDensity ε X W) S := by
      change ContinuousOn
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W *
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W) S
      exact hWIm.mul hA
    exact hc.intervalIntegrable
  have hMismatch :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_phase_plus_amplitude_integrals
      (hε := hε) hSafe hZetaInt hRateInt hPhaseInt hAmplitudeInt
  have hPhaseLedger :=
    pascalCenteredXiPrimeSideFiniteResidual_top_phase_channel_displacement_ledger_of_safe
      (X := X) hε hSafe
  have hAmplitudeLedger :=
    pascalCenteredXiPrimeSideFiniteResidual_top_amplitude_channel_displacement_ledger_of_safe
      (X := X) hε hSafe
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
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDisplacement X W) S := by
    exact intervalIntegral.continuousOn_primitive_interval'
      (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe
        hSafe X) (left_mem_uIcc : W.rectangle.σ ∈ S)
  have hDCont : ContinuousOn
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W) S := by
    exact intervalIntegral.continuousOn_primitive_interval'
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
        hSafe X) (left_mem_uIcc : W.rectangle.σ ∈ S)
  have hWeightRe' := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivativeReal_intervalIntegrable
    hε W
  have hWeightIm' := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightDerivativeImag_intervalIntegrable
    hε W
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
    hPhaseLedger, hAmplitudeLedger, hRem]
  ring

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_weighted_displacement_log_normSq_endpoint_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) :
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
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_weighted_displacement_ledger_of_safe
      (X := X) hε hSafe
  have hAmplitude :=
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
      hSafe X
  have hEndpoint :=
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_eq_log_normSq_endpoint
      (X := X) hSafe hAmplitude
  rw [hLedger, hEndpoint]

/-! A compact public certificate for the regularity layer.  It is useful to
    downstream files because it exposes the finite inputs without asking them
    to rebuild the local source arguments. -/

theorem pascalCenteredXiPrimeSideFiniteResidual_source_regularities
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualLogRate X W)
        (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) ∧
      IntervalIntegrable (pascalCenteredXiPrimeSideFiniteResidualLogRate X W)
        volume W.rectangle.σ (1 - W.rectangle.σ) ∧
      IntervalIntegrable (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W)
        volume W.rectangle.σ (1 - W.rectangle.σ) ∧
      IntervalIntegrable (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
        volume W.rectangle.σ (1 - W.rectangle.σ) := by
  exact ⟨pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe hSafe X,
    pascalCenteredXiPrimeSideFiniteResidualLogRate_intervalIntegrable_of_safe hSafe X,
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate_intervalIntegrable_of_safe hSafe X,
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate_intervalIntegrable_of_safe
      hSafe X⟩

end DkMath.RH.CFBRCProjection
