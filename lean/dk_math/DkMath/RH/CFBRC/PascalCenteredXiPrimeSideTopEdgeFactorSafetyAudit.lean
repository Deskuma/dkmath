/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideHolomorphicPhasePotentialAudit
import Mathlib.Tactic

/-!
# CS28: top-edge factor safety and finite zeta mismatch audit

This module separates the finite arithmetic potential path from the actual
fixed-Xi top edge.  The top decomposition is conditional on an explicit local
factor-safety contract.  Every zeta/PHZ comparison is a finite interval
integral; no Dirichlet-series expansion is used on the critical strip.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped Interval Topology

/-! ## CS28-A/B: the top factor-safety contract and pointwise decomposition -/

def IsPascalCenteredXiTopLogDerivDecompositionSafe
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
    let s := pascalSymmetricRectangleTopEdge u W.rectangle.T
    s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ Complex.Gammaℝ s ≠ 0

theorem pascalCenteredXiTopLogDeriv_eq_decomposed_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {u : ℝ} (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiNegLogDeriv
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
      pascalXiDecomposedNegLogDeriv
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  dsimp [IsPascalCenteredXiTopLogDerivDecompositionSafe] at hSafe
  rcases hSafe u hu with ⟨hs0, hs1, hzeta, hGamma⟩
  exact pascalCenteredXiNegLogDeriv_sub_center_eq_decomposed
    hs0 hs1 hzeta hGamma

/-! The three actual top terms are named with the same σ→1−σ orientation as
`pascalCenteredXiTopHorizontalContribution`. -/

noncomputable def pascalCenteredXiPrimeSideTopZetaContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
      pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))

noncomputable def pascalCenteredXiPrimeSideTopArchimedeanContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
      pascalXiArchimedeanLogDeriv
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))

noncomputable def pascalCenteredXiPrimeSideTopElementaryContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
      pascalXiElementaryLogDerivCorrection
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))

theorem pascalCenteredXiPrimeSideTopXiContribution_eq_decomposed_of_safe
    {ε : ℝ} (_hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
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
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow =
      pascalCenteredXiPrimeSideTopZetaContribution ε W +
        pascalCenteredXiPrimeSideTopArchimedeanContribution ε W +
        pascalCenteredXiPrimeSideTopElementaryContribution ε W := by
  unfold pascalCenteredXiTopHorizontalContribution
    pascalCenteredXiPrimeSideTopZetaContribution
    pascalCenteredXiPrimeSideTopArchimedeanContribution
    pascalCenteredXiPrimeSideTopElementaryContribution
  have hpoint : ∀ u : ℝ, u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) →
      pascalCenteredXiNegLogDeriv
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
        pascalXiDecomposedNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
    intro u hu
    exact pascalCenteredXiTopLogDeriv_eq_decomposed_of_safe hSafe hu
  rw [← intervalIntegral.integral_add hZeta hArch,
    ← intervalIntegral.integral_add (hZeta.add hArch) hElem]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) := by
    simpa [PascalCenteredXiResidueTransportWindow.toContourTransportWindow] using hu
  change pascalCenteredXiWeightedNegLogDeriv
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) = _
  simp only [pascalCenteredXiWeightedNegLogDeriv]
  rw [hpoint u hu']
  simp only [pascalXiDecomposedNegLogDeriv]
  ring

/-! ## CS28-C: finite arithmetic companion as a top path integral -/

noncomputable def pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)

theorem pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion_eq_pathIntegral
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion ε W X =
      2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand ε W X u := by
  classical
  rw [pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion_eq_oriented_endpoint_jump]
  let zpath : ℝ → ℂ := fun u =>
    pascalOrdinaryToCentered
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)
  let F : ℝ → ℂ := fun u =>
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X (zpath u)
  have hweight : ∀ z : ℂ,
      pascalCenteredXiMellinSecondDifferenceWeight ε 0 z =
        mellinQuadraticBoxWeight ε z := by
    intro z
    rw [pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
      hε]
    rfl
  have hzpath : ∀ u : ℝ, HasDerivAt zpath 1 u := by
    intro u
    change HasDerivAt
      (fun u : ℝ => (u : ℂ) + (W.rectangle.T : ℂ) * Complex.I - criticalLineCenter)
      1 u
    simpa [zpath, pascalOrdinaryToCentered, pascalSymmetricRectangleTopEdge] using
      (((hasDerivAt_id (u : ℂ)).comp_ofReal).add_const
        ((W.rectangle.T : ℂ) * Complex.I - criticalLineCenter))
  have hderiv : ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      HasDerivAt F
        (2 * pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
          ε W X u) u := by
    intro u hu
    have hterm : ∀ n : ℕ, HasDerivAt
        (fun v : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (pascalCenteredXiPrimeSideComplexModePhasePotential ε n ∘ zpath) v)
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          (mellinQuadraticBoxWeight ε (zpath u) *
            (n : ℂ) ^ (-(criticalLineCenter + zpath u)) * (1 : ℂ))) u := by
      intro n
      by_cases hn0 : n = 0
      · subst n
        have hm0 : HasDerivAt
            (pascalCenteredXiPrimeSideComplexModePhasePotential ε 0)
            0 (zpath u) := by
          have hfun : pascalCenteredXiPrimeSideComplexModePhasePotential ε 0 =
              (fun _ : ℂ => (0 : ℂ)) := by
            funext z
            simp [pascalCenteredXiPrimeSideComplexModePhasePotential]
          rw [hfun]
          exact hasDerivAt_const (zpath u) 0
        have hs0 := (hm0.comp u (hzpath u)).const_mul
          (ArithmeticFunction.vonMangoldt 0 : ℂ)
        simpa [vonMangoldtComplexCoeff_zero, mul_one] using hs0
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hm := pascalCenteredXiPrimeSideComplexModePhasePotential_hasDerivAt
          hε hnpos (zpath u)
        exact (hm.comp u (hzpath u)).const_mul
          (ArithmeticFunction.vonMangoldt n : ℂ)
    have hsum : HasDerivAt
        (∑ n ∈ Finset.range (X + 1), fun v : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (pascalCenteredXiPrimeSideComplexModePhasePotential ε n ∘ zpath) v)
        (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (mellinQuadraticBoxWeight ε (zpath u) *
              (n : ℂ) ^ (-(criticalLineCenter + zpath u)) * (1 : ℂ))) u := by
      exact HasDerivAt.sum (u := Finset.range (X + 1))
        (fun n hn => hterm n)
    have hF : HasDerivAt F
        ((2 : ℂ) * ∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((mellinQuadraticBoxWeight ε (zpath u) *
              (n : ℂ) ^ (-(criticalLineCenter + zpath u))) * 1)) u := by
      have hs := hsum.const_mul (2 : ℂ)
      simpa [F, pascalCenteredXiPrimeSideAggregateComplexPhasePotential] using hs
    have hsource :
        2 * pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
          ε W X u =
        2 * (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((mellinQuadraticBoxWeight ε (zpath u) *
              (n : ℂ) ^ (-(criticalLineCenter + zpath u))) * 1)) := by
      unfold pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
      rw [pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum]
      rw [Finset.mul_sum]
      apply congrArg (fun z : ℂ => 2 * z)
      apply Finset.sum_congr rfl
      intro n hn
      rw [hweight]
      have he : -(pascalSymmetricRectangleTopEdge u W.rectangle.T) =
          -(criticalLineCenter + zpath u) := by
        simp [zpath, pascalOrdinaryToCentered, pascalSymmetricRectangleTopEdge,
          criticalLineCenter]
      rw [he]
      simp [zpath]
      ring
    rw [hsource]
    exact hF
  have hcont : ContinuousOn F
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
    intro u hu
    exact (hderiv u hu).continuousAt.continuousWithinAt
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    hcont
    (fun u hu => (hderiv u (mem_Icc_of_Ioo hu)).hasDerivWithinAt)
    ((by
      have hc : Continuous
          (fun u : ℝ =>
            2 * pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
              ε W X u) := by
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
          · let _ : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
            have hnterm : (fun u : ℝ =>
                LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
                  (pascalSymmetricRectangleTopEdge u W.rectangle.T) n) =
              (fun u : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
                ((n : ℂ) ^ (-(pascalSymmetricRectangleTopEdge u W.rectangle.T)))) := by
              funext u
              rw [vonMangoldt_LSeries_term_eq]
            rw [hnterm]
            have hc : Continuous (fun u : ℝ =>
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  ((n : ℂ) ^ (-(pascalSymmetricRectangleTopEdge u W.rectangle.T)))) :=
              continuous_const.mul
                ((continuous_const_cpow (n : ℂ)).comp
                  (continuous_neg.comp hpath))
            exact hc
        have hphz : Continuous (fun u : ℝ => pascalPrimePowerPHZFiniteUpTo X
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
        exact continuous_const.mul ((hw.comp hz).mul hphz)
      exact hc.intervalIntegrable (μ := volume)
        W.rectangle.σ (1 - W.rectangle.σ)))
  convert hfund.symm using 1 <;>
    simp [F, zpath, pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand,
      pascalOrdinaryToCentered, pascalSymmetricRectangleTopEdge, criticalLineCenter]
  ring_nf

/-! ## CS28-D: the finite zeta-cutoff mismatch -/

noncomputable def pascalCenteredXiPrimeSideTopZetaCutoffMismatch
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
      pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) -
  (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))

theorem pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_finite_difference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X =
      (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalXiOrdinaryZetaNegLogDeriv
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))) -
        (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
            ε W X u) := by
  unfold pascalCenteredXiPrimeSideTopZetaCutoffMismatch
    pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand
  ring

theorem pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_zero_of_exact_source
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hExact : ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) =
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) :
    pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X = 0 := by
  unfold pascalCenteredXiPrimeSideTopZetaCutoffMismatch
  have hEq : (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
      (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalPrimePowerPHZFiniteUpTo X
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    dsimp
    rw [hExact u hu]
  have hEq2 := congrArg (fun z : ℂ => 2 * z) hEq
  rw [hEq2]
  ring

/-! ## CS28-E/F: exact finite ledger and corner separation -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatch_ledger
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
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
    (X : ℕ) :
    2 * pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow =
      pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion ε W X +
      2 * pascalCenteredXiPrimeSideTopArchimedeanContribution ε W +
      2 * pascalCenteredXiPrimeSideTopElementaryContribution ε W +
      pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X := by
  rw [pascalCenteredXiPrimeSideTopXiContribution_eq_decomposed_of_safe hε hSafe
    hZeta hArch hElem]
  rw [pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion_eq_pathIntegral
    hε W X]
  rw [pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_finite_difference]
  unfold pascalCenteredXiPrimeSideTopZetaContribution
    pascalCenteredXiPrimeSideTopArchimedeanContribution
    pascalCenteredXiPrimeSideTopElementaryContribution
  ring

/-! The common potential gives a corner identity, but this is not a claim that
the vertical interaction equals the top companion. -/

theorem pascalCenteredXiPrimeSideFiniteTopCompanion_is_separate_corner_difference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion ε W X =
      pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
        (-((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
          (W.rectangle.T : ℂ) * Complex.I) -
      pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
        (((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
          (W.rectangle.T : ℂ) * Complex.I) := by
  rfl

/-! ## CS28-G: the narrowed analytic frontier -/

inductive PascalCenteredXiPrimeSideFiniteTopZetaMismatchGap : Prop
  | noIndependentFiniteTopZetaMismatchEstimate

end DkMath.RH.CFBRCProjection
