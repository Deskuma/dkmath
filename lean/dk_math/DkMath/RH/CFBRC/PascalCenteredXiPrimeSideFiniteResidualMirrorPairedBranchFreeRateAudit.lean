/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedFunctionalEquationAudit
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

/-!
# CS37: branch-free rate decomposition of the finite mirror pair

This module lifts the CS36 value factorisation to an exact local rate
identity.  The completed-zeta, Gamma, and finite PHZ pieces are kept as
separate branch-free terms.  Everything is pointwise at a safe finite top
point; no logarithm branch, limiting product, sign estimate, or RH argument is
introduced.
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

/-! ## CS37-A/C: local completed-zeta rate -/

noncomputable def pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate
    (s : ℂ) : ℂ :=
  -logDeriv completedRiemannZeta s

private theorem differentiableAt_GammaR_cs37
    {s : ℂ} (hGamma : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hi : DifferentiableAt ℂ (fun t : ℂ => (Complex.Gammaℝ t)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hii := hi.inv (inv_ne_zero hGamma)
  have hfun : (fun t : ℂ => ((Complex.Gammaℝ t)⁻¹)⁻¹) =
      Complex.Gammaℝ := by
    funext t
    simp only [inv_inv]
  rw [← hfun]
  exact hii

private theorem gammaR_ne_zero_eventually_cs37
    {s : ℂ} (hGamma : Complex.Gammaℝ s ≠ 0) :
    ∀ᶠ t in 𝓝 s, Complex.Gammaℝ t ≠ 0 := by
  have hi_event : ∀ᶠ t in 𝓝 s, (Complex.Gammaℝ t)⁻¹ ≠ 0 :=
    (Complex.differentiable_Gammaℝ_inv.continuous.continuousAt).eventually_ne
      (inv_ne_zero hGamma)
  filter_upwards [hi_event] with t ht
  intro hzero
  exact ht (by simp [hzero])

theorem pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate_eq_ordinary_add_gamma
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate s =
      pascalXiOrdinaryZetaNegLogDeriv s +
        pascalXiArchimedeanLogDeriv s := by
  have hzf : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hgf : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_GammaR_cs37 hGamma
  have hcompletedEq : completedRiemannZeta =ᶠ[𝓝 s]
      (fun t : ℂ => riemannZeta t * Complex.Gammaℝ t) := by
    filter_upwards [eventually_ne_nhds hs0,
      gammaR_ne_zero_eventually_cs37 hGamma] with t ht0 htGamma
    exact completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero
      ht0 htGamma
  have hlog : logDeriv completedRiemannZeta s =
      logDeriv (fun t : ℂ => riemannZeta t * Complex.Gammaℝ t) s := by
    rw [logDeriv_apply, logDeriv_apply,
      hcompletedEq.deriv_eq, hcompletedEq.eq_of_nhds]
  have hprod : logDeriv (fun t : ℂ =>
      riemannZeta t * Complex.Gammaℝ t) s =
      logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s := by
    rw [logDeriv_mul (f := riemannZeta) (g := Complex.Gammaℝ) s
      hzeta hGamma hzf hgf]
  unfold pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate
    pascalXiOrdinaryZetaNegLogDeriv pascalXiArchimedeanLogDeriv
  rw [hlog, hprod]
  simp only [logDeriv_apply, div_eq_mul_inv]
  ring

theorem pascalCenteredXiPrimeSideFiniteOrdinaryZetaNegLogRate_eq_completed_sub_gamma
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    pascalXiOrdinaryZetaNegLogDeriv s =
      pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate s -
        pascalXiArchimedeanLogDeriv s := by
  rw [pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate_eq_ordinary_add_gamma
    hs0 hs1 hzeta hGamma]
  ring

private theorem pascalXiOrdinaryZetaNegLogDeriv_conj_cs37 (s : ℂ) :
    pascalXiOrdinaryZetaNegLogDeriv (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalXiOrdinaryZetaNegLogDeriv s) := by
  have hfun : (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) =
      riemannZeta := by
    funext z
    simp [Function.comp_def, riemannZeta_conj]
  have hderiv := congrFun (deriv_conj_conj (f := riemannZeta))
    (starRingEnd ℂ s)
  have hderiv' : deriv riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv riemannZeta s) := by
    rw [← hfun] at hderiv
    simpa [Function.comp_def] using hderiv
  unfold pascalXiOrdinaryZetaNegLogDeriv
  rw [hderiv', riemannZeta_conj]
  simp

/-! ## CS37-D: finite symmetric Euler rate -/

noncomputable def pascalCenteredXiPrimeSideFiniteSymmetricEulerRate
    (X : ℕ) (s : ℂ) : ℂ :=
  pascalPrimePowerPHZFiniteUpTo X (1 - s) -
    pascalPrimePowerPHZFiniteUpTo X s

theorem pascalCenteredXiPrimeSideFiniteSymmetricEulerRate_conj
    (X : ℕ) (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
        (starRingEnd ℂ s) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s) := by
  unfold pascalCenteredXiPrimeSideFiniteSymmetricEulerRate
  rw [map_sub]
  have harg : 1 - starRingEnd ℂ s = starRingEnd ℂ (1 - s) := by
    simp only [map_sub, map_one, starRingEnd_apply]
  rw [harg, pascalPrimePowerPHZFiniteUpTo_conj,
    pascalPrimePowerPHZFiniteUpTo_conj]

/-! ## CS37-E: the paired branch-free rate ledger -/

noncomputable def pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
    (s : ℂ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate s -
    pascalCenteredXiPrimeSideFiniteCompletedZetaNegLogRate (1 - s)

noncomputable def pascalCenteredXiPrimeSideFiniteGammaMirrorRate
    (s : ℂ) : ℂ :=
  -pascalXiArchimedeanLogDeriv s +
    pascalXiArchimedeanLogDeriv (1 - s)

noncomputable def pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate
    (X : ℕ) (s : ℂ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate s +
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate s +
    pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorRate_eq_functionalEquationRate
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u =
      pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  dsimp [pascalCenteredXiPrimeSideFiniteResidualMirrorRate,
    pascalCenteredXiPrimeSideFiniteResidualLogRate,
    pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate,
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate,
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate,
    pascalCenteredXiPrimeSideFiniteSymmetricEulerRate]
  dsimp [IsPascalCenteredXiTopLogDerivDecompositionSafe] at hSafe
  have hs := hSafe u hu
  have hmirror := pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror hu
  have hm := hSafe (1 - u) hmirror
  let s : ℂ := pascalSymmetricRectangleTopEdge u W.rectangle.T
  let m : ℂ := pascalSymmetricRectangleTopEdge (1 - u) W.rectangle.T
  have hs_def : s = pascalSymmetricRectangleTopEdge u W.rectangle.T := rfl
  have hm_def : m = pascalSymmetricRectangleTopEdge (1 - u) W.rectangle.T := rfl
  have hsm : starRingEnd ℂ m = 1 - s := by
    dsimp [s, m]
    exact pascalCenteredXiPrimeSideFiniteResidualMirror_conj_top_eq_one_sub
      u W.rectangle.T
  have hq_s := pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
    (X := X) hs.2.1 hs.2.2.1
  have hq_m := pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
    (X := X) hm.2.1 hm.2.2.1
  have hq_m_conj := congrArg (starRingEnd ℂ) hq_m
  have hq_m_conj' :
      starRingEnd ℂ
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z) m) =
        pascalXiOrdinaryZetaNegLogDeriv (1 - s) -
          pascalPrimePowerPHZFiniteUpTo X (1 - s) := by
    rw [map_sub,
      ← pascalXiOrdinaryZetaNegLogDeriv_conj_cs37 m,
      ← pascalPrimePowerPHZFiniteUpTo_conj X m] at hq_m_conj
    simpa only [hsm, starRingEnd_apply, star_star] using hq_m_conj
  rw [hq_s, hq_m_conj']
  have href0 : 1 - s ≠ 0 := by
    intro h
    apply hm.1
    have hz : starRingEnd ℂ m = 0 := by rw [hsm, h]
    simpa only [starRingEnd_apply, map_zero, star_star] using
      congrArg (starRingEnd ℂ) hz
  have href1 : 1 - s ≠ 1 := by
    intro h
    apply hm.2.1
    have hz : starRingEnd ℂ m = 1 := by rw [hsm, h]
    simpa only [starRingEnd_apply, star_star, map_one] using
      congrArg (starRingEnd ℂ) hz
  have hzref : riemannZeta (1 - s) ≠ 0 := by
    intro h
    apply hm.2.2.1
    have heq : riemannZeta (1 - s) =
        starRingEnd ℂ (riemannZeta m) := by
      rw [← hsm]
      exact riemannZeta_conj m
    have hz : starRingEnd ℂ (riemannZeta m) = 0 := by rw [← heq, h]
    simpa using hz
  have hGref : Complex.Gammaℝ (1 - s) ≠ 0 := by
    intro h
    apply hm.2.2.2
    have heq : Complex.Gammaℝ (1 - s) =
        starRingEnd ℂ (Complex.Gammaℝ m) := by
      rw [← hsm]
      exact pascalXiArchimedeanGammaR_conj m
    have hz : starRingEnd ℂ (Complex.Gammaℝ m) = 0 := by rw [← heq, h]
    simpa using hz
  have hO_s := pascalCenteredXiPrimeSideFiniteOrdinaryZetaNegLogRate_eq_completed_sub_gamma
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have hO_ref := pascalCenteredXiPrimeSideFiniteOrdinaryZetaNegLogRate_eq_completed_sub_gamma
    href0 href1 hzref hGref
  rw [hO_s, hO_ref]
  ring

theorem pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate_mirror
    (X : ℕ) (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate X (1 - s) =
      -pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate X s := by
  unfold pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate
    pascalCenteredXiPrimeSideFiniteSymmetricEulerRate
  have h : 1 - (1 - s) = s := by ring
  rw [h]
  ring

theorem pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate_center
    (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate X
        (1 / 2 : ℂ) = 0 := by
  unfold pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate
    pascalCenteredXiPrimeSideFiniteSymmetricEulerRate
  have h : (1 : ℂ) - (1 / 2 : ℂ) = 1 / 2 := by norm_num
  rw [h]
  ring

/-! ## CS37-F: explicit no-cancellation marker -/

inductive PascalCenteredXiPrimeSideFiniteResidualMirrorPairedRateCancellationGap : Prop
  | no_exact_rectangle_background_cancellation_from_rate_ledger

end DkMath.RH.CFBRCProjection
