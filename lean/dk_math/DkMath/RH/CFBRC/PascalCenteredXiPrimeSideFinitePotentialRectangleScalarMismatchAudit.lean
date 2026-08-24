/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideTopEdgeFactorSafetyAudit
import Mathlib.Tactic

/-!
# CS29: finite potential rectangle and scalar-mismatch audit

This module records only finite algebraic and finite-path consequences of the
CS27 holomorphic potential and the CS28 top ledger.  The normalization by
`(2 * π * I)⁻¹` is projected to its surviving imaginary component.  The four
finite arithmetic edge companions telescope, but that telescope is kept
separate from the fixed-Xi top mismatch.  No norm estimate, infinite
exchange, endpoint sign, or RH conclusion is asserted.
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

/-! ## CS29-A: the normalized scalar adapter -/

theorem normalized_by_two_pi_i_re
    (z : ℂ) :
    (((2 * Real.pi * Complex.I)⁻¹) * z).re =
      z.im / (2 * Real.pi) := by
  simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

noncomputable def pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X).re

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_im_div_two_pi
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X).im /
        (2 * Real.pi) := by
  unfold pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar
  exact normalized_by_two_pi_i_re _

/-! ## CS29-B: conjugation of the finite holomorphic source -/

theorem pascalCenteredXiPrimeSideComplexPhasePotential_conj
    (r : ℝ) (z : ℂ) :
    pascalCenteredXiPrimeSideComplexPhasePotential r
        (starRingEnd ℂ z) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideComplexPhasePotential r z) := by
  by_cases hr : r = 0
  · subst r
    simp only [pascalCenteredXiPrimeSideComplexPhasePotential, if_pos]
    rw [map_div₀, map_pow]
    have htwo : starRingEnd ℂ (2 : ℂ) = (2 : ℂ) := by
      simp only [map_ofNat]
    rw [htwo]
  · rw [pascalCenteredXiPrimeSideComplexPhasePotential,
      if_neg hr]
    simp only [pascalCenteredXiPrimeSideComplexPhasePotential, if_neg hr]
    rw [map_div₀]
    simp only [map_mul, map_sub, map_pow]
    have harg : (r : ℂ) * starRingEnd ℂ z =
        starRingEnd ℂ ((r : ℂ) * z) := by
      simp
    rw [harg, Complex.exp_conj]
    simp

theorem pascalCenteredXiPrimeSideComplexModePhasePotential_conj
    (ε : ℝ) (n : ℕ) (z : ℂ) :
    pascalCenteredXiPrimeSideComplexModePhasePotential ε n
        (starRingEnd ℂ z) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideComplexModePhasePotential ε n z) := by
  by_cases hn : n = 0
  · subst n
    simp [pascalCenteredXiPrimeSideComplexModePhasePotential]
  · simp only [pascalCenteredXiPrimeSideComplexModePhasePotential, if_neg hn,
      map_mul, map_sub]
    rw [pascalCenteredXiPrimeSideComplexPhasePotential_conj,
      pascalCenteredXiPrimeSideComplexPhasePotential_conj]
    simp

theorem pascalCenteredXiPrimeSideAggregateComplexPhasePotential_conj
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (z : ℂ) :
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
        (starRingEnd ℂ z) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X z) := by
  unfold pascalCenteredXiPrimeSideAggregateComplexPhasePotential
  simp only [map_mul, map_sum]
  have htwo : starRingEnd ℂ (2 : ℂ) = (2 : ℂ) := by
    simp only [map_ofNat]
  rw [htwo]
  apply congrArg (fun q : ℂ => (2 : ℂ) * q)
  apply Finset.sum_congr rfl
  intro n hn
  have hcoeff : starRingEnd ℂ (ArithmeticFunction.vonMangoldt n : ℂ) =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by simp
  rw [hcoeff, pascalCenteredXiPrimeSideComplexModePhasePotential_conj]

theorem pascalCenteredXiPrimeSideComplexModePhasePotential_ofReal_im
    (ε : ℝ) (n : ℕ) (a : ℝ) :
    (pascalCenteredXiPrimeSideComplexModePhasePotential ε n (a : ℂ)).im = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [pascalCenteredXiPrimeSideComplexModePhasePotential]
  · simp only [pascalCenteredXiPrimeSideComplexModePhasePotential, if_neg hn,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_im]
    rw [pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im,
      pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im]
    ring

theorem pascalCenteredXiPrimeSideAggregateComplexPhasePotential_ofReal_im
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (a : ℝ) :
    (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (a : ℂ)).im = 0 := by
  unfold pascalCenteredXiPrimeSideAggregateComplexPhasePotential
  simp only [Complex.mul_im, Complex.im_sum, Complex.ofReal_im]
  simp_rw [pascalCenteredXiPrimeSideComplexModePhasePotential_ofReal_im]
  norm_num

/-! ## CS29-C: centered rectangle corners -/

noncomputable def pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner
    (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
    (W.rectangle.T : ℂ) * Complex.I

noncomputable def pascalCenteredXiPrimeSideFiniteRectangleTopLeftCorner
    (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  -((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
    (W.rectangle.T : ℂ) * Complex.I

noncomputable def pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner
    (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) -
    (W.rectangle.T : ℂ) * Complex.I

noncomputable def pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner
    (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  -((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) -
    (W.rectangle.T : ℂ) * Complex.I

theorem pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner_eq_conj_topRight
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner W =
      starRingEnd ℂ (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W) := by
  apply Complex.ext <;>
    simp [pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner,
      pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner]

theorem pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner_eq_conj_topLeft
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner W =
      starRingEnd ℂ (pascalCenteredXiPrimeSideFiniteRectangleTopLeftCorner W) := by
  apply Complex.ext <;>
    simp [pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner,
      pascalCenteredXiPrimeSideFiniteRectangleTopLeftCorner]

/-! ## CS29-D/E: finite edge companions and the rectangle telescope -/

noncomputable def pascalCenteredXiPrimeSideFiniteRightCompanion
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W) -
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner W)

noncomputable def pascalCenteredXiPrimeSideFiniteTopCompanion
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleTopLeftCorner W) -
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W)

noncomputable def pascalCenteredXiPrimeSideFiniteLeftCompanion
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner W) -
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleTopLeftCorner W)

noncomputable def pascalCenteredXiPrimeSideFiniteBottomCompanion
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner W) -
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner W)

theorem pascalCenteredXiPrimeSideFiniteTopCompanion_eq_existing
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteTopCompanion ε W X =
      pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion ε W X := by
  rfl

theorem pascalCenteredXiPrimeSideFiniteRectangleCompanions_telescope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRightCompanion ε W X +
        pascalCenteredXiPrimeSideFiniteTopCompanion ε W X +
        pascalCenteredXiPrimeSideFiniteLeftCompanion ε W X +
        pascalCenteredXiPrimeSideFiniteBottomCompanion ε W X = 0 := by
  unfold pascalCenteredXiPrimeSideFiniteRightCompanion
    pascalCenteredXiPrimeSideFiniteTopCompanion
    pascalCenteredXiPrimeSideFiniteLeftCompanion
    pascalCenteredXiPrimeSideFiniteBottomCompanion
  ring

theorem pascalCenteredXiPrimeSideFiniteBottomCompanion_eq_neg_conj_top
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteBottomCompanion ε W X =
      -starRingEnd ℂ (pascalCenteredXiPrimeSideFiniteTopCompanion ε W X) := by
  unfold pascalCenteredXiPrimeSideFiniteBottomCompanion
    pascalCenteredXiPrimeSideFiniteTopCompanion
  rw [pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner_eq_conj_topRight,
    pascalCenteredXiPrimeSideFiniteRectangleBottomLeftCorner_eq_conj_topLeft,
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential_conj,
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential_conj]
  simp only [map_sub]
  ring

theorem pascalCenteredXiPrimeSideFiniteTopCompanion_add_bottom_eq_two_i_im
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteTopCompanion ε W X +
        pascalCenteredXiPrimeSideFiniteBottomCompanion ε W X =
      2 * Complex.I *
        (pascalCenteredXiPrimeSideFiniteTopCompanion ε W X).im := by
  rw [pascalCenteredXiPrimeSideFiniteBottomCompanion_eq_neg_conj_top]
  apply Complex.ext
  all_goals simp [Complex.mul_re, Complex.mul_im]
  ring

/-! The finite telescope is deliberately not a fixed-Xi mismatch estimate. -/

inductive PascalCenteredXiPrimeSideFiniteRectangleClosureGap : Prop
  | actualFixedXiTopStillSeparate

/-! ## CS29-F: right-edge finite potential path -/

noncomputable def pascalCenteredXiPrimeSideFiniteRightPathIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t) * Complex.I

theorem pascalCenteredXiPrimeSideFiniteRightCompanion_eq_pathIntegral
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRightCompanion ε W X =
      2 * ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideFiniteRightPathIntegrand ε W X t := by
  classical
  let zpath : ℝ → ℂ := fun t =>
    ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) + Complex.I * (t : ℂ)
  let F : ℝ → ℂ := fun t =>
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X (zpath t)
  have hzpath : ∀ t : ℝ, HasDerivAt zpath Complex.I t := by
    intro t
    have h := (((hasDerivAt_id (t : ℂ)).comp_ofReal).const_mul Complex.I).add_const
        (((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ))
    simpa [zpath] using h
  have hderiv : ∀ t ∈ Set.uIcc (-W.rectangle.T) W.rectangle.T,
      HasDerivAt F
        (2 * pascalCenteredXiPrimeSideFiniteRightPathIntegrand ε W X t) t := by
    intro t ht
    have hterm : ∀ n : ℕ, HasDerivAt
        (fun v : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (pascalCenteredXiPrimeSideComplexModePhasePotential ε n ∘ zpath) v)
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          (mellinQuadraticBoxWeight ε (zpath t) *
            (n : ℂ) ^ (-(criticalLineCenter + zpath t)) * Complex.I)) t := by
      intro n
      by_cases hn0 : n = 0
      · subst n
        have hm0 : HasDerivAt
            (pascalCenteredXiPrimeSideComplexModePhasePotential ε 0)
            0 (zpath t) := by
          have hfun : pascalCenteredXiPrimeSideComplexModePhasePotential ε 0 =
              (fun _ : ℂ => (0 : ℂ)) := by
            funext z
            simp [pascalCenteredXiPrimeSideComplexModePhasePotential]
          rw [hfun]
          exact hasDerivAt_const (zpath t) 0
        have hs0 := (hm0.comp t (hzpath t)).const_mul
          (ArithmeticFunction.vonMangoldt 0 : ℂ)
        simpa [vonMangoldtComplexCoeff_zero, mul_one] using hs0
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hm := pascalCenteredXiPrimeSideComplexModePhasePotential_hasDerivAt
          hε hnpos (zpath t)
        have hc := hm.comp t (hzpath t)
        have hc' := hc.const_mul (ArithmeticFunction.vonMangoldt n : ℂ)
        simpa [mul_assoc] using hc'
    have hsum : HasDerivAt
        (∑ n ∈ Finset.range (X + 1), fun v : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (pascalCenteredXiPrimeSideComplexModePhasePotential ε n ∘ zpath) v)
        (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (mellinQuadraticBoxWeight ε (zpath t) *
              (n : ℂ) ^ (-(criticalLineCenter + zpath t)) * Complex.I)) t := by
      exact HasDerivAt.sum (u := Finset.range (X + 1))
        (fun n hn => hterm n)
    have hF := hsum.const_mul (2 : ℂ)
    have hF' : HasDerivAt F
        ((2 : ℂ) * ∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (mellinQuadraticBoxWeight ε (zpath t) *
              (n : ℂ) ^ (-(criticalLineCenter + zpath t)) * Complex.I)) t := by
      simpa [F, pascalCenteredXiPrimeSideAggregateComplexPhasePotential] using hF
    have hsource :
        2 * pascalCenteredXiPrimeSideFiniteRightPathIntegrand ε W X t =
        (2 : ℂ) * ∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (mellinQuadraticBoxWeight ε (zpath t) *
              (n : ℂ) ^ (-(criticalLineCenter + zpath t)) * Complex.I) := by
      have hweight : ∀ z : ℂ,
          pascalCenteredXiMellinSecondDifferenceWeight ε 0 z =
            mellinQuadraticBoxWeight ε z := by
        intro z
        rw [pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
          hε]
        rfl
      unfold pascalCenteredXiPrimeSideFiniteRightPathIntegrand
      rw [pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum]
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply congrArg (fun z : ℂ => 2 * z)
      apply Finset.sum_congr rfl
      intro n hn
      rw [hweight]
      have hz : pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t) = zpath t := by
        simp [zpath, pascalOrdinaryToCentered, pascalSymmetricRectangleRightEdge, criticalLineCenter]
        ring
      rw [hz]
      have he : -(pascalSymmetricRectangleRightEdge W.rectangle.σ t) =
          -(criticalLineCenter + zpath t) := by
        simp [zpath, pascalSymmetricRectangleRightEdge, criticalLineCenter]
        ring
      rw [he]
      ring
    rw [hsource]
    exact hF'
  have hcont : ContinuousOn F
      (Set.uIcc (-W.rectangle.T) W.rectangle.T) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    hcont
    (fun t ht => (hderiv t (mem_Icc_of_Ioo ht)).hasDerivWithinAt)
    ((by
      have hc : Continuous
          (fun t : ℝ => 2 * pascalCenteredXiPrimeSideFiniteRightPathIntegrand
            ε W X t) := by
        have hpath : Continuous (fun t : ℝ =>
            pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
          change Continuous (fun t : ℝ =>
            (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
          fun_prop
        have hw := (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
          (ε := ε) (τ := 0) hε).continuous
        have hz : Continuous (fun t : ℝ =>
            pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
          change Continuous (fun t : ℝ =>
            ((W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I) - criticalLineCenter)
          fun_prop
        have hphz : Continuous (fun t : ℝ =>
            pascalPrimePowerPHZFiniteUpTo X
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
          rw [show (fun t : ℝ => pascalPrimePowerPHZFiniteUpTo X
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) =
          (fun t : ℝ => ∑ n ∈ Finset.range (X + 1),
            LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) by
            funext t
            exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _]
          apply continuous_finsetSum
          intro n hn
          by_cases hn0 : n = 0
          · subst n
            simpa [vonMangoldt_LSeries_term_eq] using
              (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
          · let _ : NeZero (n : ℂ) := ⟨by exact_mod_cast hn0⟩
            have htermEq : (fun t : ℝ =>
              LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
                (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) =
              (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
                ((n : ℂ) ^ (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) := by
                funext t
                rw [vonMangoldt_LSeries_term_eq]
            rw [htermEq]
            have hterm : Continuous (fun t : ℝ =>
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  ((n : ℂ) ^ (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) :=
              continuous_const.mul
                ((continuous_const_cpow (n : ℂ)).comp
                  (continuous_neg.comp hpath))
            simpa using hterm
        have hbase : Continuous
            (fun t : ℝ => pascalCenteredXiPrimeSideFiniteRightPathIntegrand
              ε W X t) := by
          have hbase0 : Continuous (fun t : ℝ =>
              pascalCenteredXiMellinSecondDifferenceWeight ε 0
                  (pascalOrdinaryToCentered
                    (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
                pascalPrimePowerPHZFiniteUpTo X
                  (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) :=
            (hw.comp hz).mul hphz
          have hc0 : Continuous (fun t : ℝ =>
              (pascalCenteredXiMellinSecondDifferenceWeight ε 0
                  (pascalOrdinaryToCentered
                    (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
                pascalPrimePowerPHZFiniteUpTo X
                  (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
                Complex.I) :=
            hbase0.mul continuous_const
          convert hc0 using 1
          funext t
          simp [pascalCenteredXiPrimeSideFiniteRightPathIntegrand]
        have hc0 : Continuous (fun t : ℝ =>
            (2 : ℂ) * pascalCenteredXiPrimeSideFiniteRightPathIntegrand
              ε W X t) := continuous_const.mul hbase
        convert hc0 using 1
      exact hc.intervalIntegrable (μ := volume)
        (-W.rectangle.T) W.rectangle.T))
  calc
    pascalCenteredXiPrimeSideFiniteRightCompanion ε W X =
        F W.rectangle.T - F (-W.rectangle.T) := by
      dsimp [F, zpath,
        pascalCenteredXiPrimeSideFiniteRightCompanion,
        pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner,
        pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner,
        pascalOrdinaryToCentered, pascalSymmetricRectangleRightEdge,
        criticalLineCenter]
      have hargTop : ((W.rectangle.σ : ℂ) - ((1 / 2 : ℝ) : ℂ) +
          (W.rectangle.T : ℂ) * Complex.I) =
          ((W.rectangle.σ : ℂ) - ((1 / 2 : ℝ) : ℂ) +
            Complex.I * ((W.rectangle.T : ℝ) : ℂ)) := by
        ring
      have harg : ((W.rectangle.σ : ℂ) - ((1 / 2 : ℝ) : ℂ) -
          (W.rectangle.T : ℂ) * Complex.I) =
          ((W.rectangle.σ : ℂ) - ((1 / 2 : ℝ) : ℂ) +
            Complex.I * ((-W.rectangle.T : ℝ) : ℂ)) := by
        simp only [Complex.ofReal_neg]
        ring
      rw [hargTop, harg]
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
        2 * pascalCenteredXiPrimeSideFiniteRightPathIntegrand ε W X t :=
      hfund.symm
    _ = 2 * ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideFiniteRightPathIntegrand ε W X t := by
      rw [intervalIntegral.integral_const_mul]

/-! ## CS29-F/G: interaction identification and normalized top ledger -/

theorem pascalCenteredXiPrimeSideFiniteRightCompanion_eq_two_i_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRightCompanion ε W X =
      2 * Complex.I *
        (pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X : ℂ) := by
  have hI := pascalCenteredXiPrimeSideAggregateInteraction_eq_im_complexAggregatePhaseJump
    hε W X
  have hI' : pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W) -
        pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          (((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ)).im := by
    simpa [pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner] using hI
  have hreal := pascalCenteredXiPrimeSideAggregateComplexPhasePotential_ofReal_im
    ε W X (W.rectangle.σ - (1 / 2 : ℝ))
  calc
    pascalCenteredXiPrimeSideFiniteRightCompanion ε W X =
        pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
            (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W) -
          pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
            (pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner W) := rfl
    _ = pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W) -
        starRingEnd ℂ
          (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
            (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W)) := by
      rw [pascalCenteredXiPrimeSideFiniteRectangleBottomRightCorner_eq_conj_topRight,
        pascalCenteredXiPrimeSideAggregateComplexPhasePotential_conj]
    _ = 2 * Complex.I *
        (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W)).im := by
      apply Complex.ext
      all_goals simp [Complex.mul_re, Complex.mul_im]
      ring
    _ = 2 * Complex.I *
        (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
            (pascalCenteredXiPrimeSideFiniteRectangleTopRightCorner W) -
          pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
            (((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ)).im := by
      rw [Complex.sub_im, hreal]
      ring_nf
    _ = 2 * Complex.I *
        (pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X : ℂ) := by
      rw [hI']

theorem pascalCenteredXiPrimeSideFiniteRightCompanion_normalized_re_eq_interaction_div_pi
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (((2 * Real.pi * Complex.I)⁻¹) *
      pascalCenteredXiPrimeSideFiniteRightCompanion ε W X).re =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X /
        Real.pi := by
  rw [pascalCenteredXiPrimeSideFiniteRightCompanion_eq_two_i_interaction hε W X,
    normalized_by_two_pi_i_re]
  simp [Complex.mul_re, Complex.mul_im]
  field_simp [Real.pi_ne_zero]

noncomputable def pascalCenteredXiPrimeSideFiniteTopArithmeticCompanionScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    pascalCenteredXiPrimeSideFiniteTopCompanion ε W X).re

noncomputable def pascalCenteredXiPrimeSideFiniteTopArchimedeanCompanionScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    pascalCenteredXiPrimeSideTopArchimedeanContribution ε W).re

noncomputable def pascalCenteredXiPrimeSideFiniteTopElementaryCompanionScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    pascalCenteredXiPrimeSideTopElementaryContribution ε W).re

noncomputable def pascalCenteredXiPrimeSideFiniteNormalizedTopContribution
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    (2 * pascalCenteredXiTopHorizontalContribution
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.toContourTransportWindow)).re

theorem pascalCenteredXiPrimeSideFiniteNormalizedTopLedger
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
    pascalCenteredXiPrimeSideFiniteNormalizedTopContribution ε W =
      (((2 * Real.pi * Complex.I)⁻¹) *
        pascalCenteredXiPrimeSideFiniteTopCompanion ε W X).re +
      (((2 * Real.pi * Complex.I)⁻¹) *
        (2 * pascalCenteredXiPrimeSideTopArchimedeanContribution ε W)).re +
      (((2 * Real.pi * Complex.I)⁻¹) *
        (2 * pascalCenteredXiPrimeSideTopElementaryContribution ε W)).re +
      pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X := by
  unfold pascalCenteredXiPrimeSideFiniteNormalizedTopContribution
  rw [pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_im_div_two_pi]
  have hledger := pascalCenteredXiPrimeSideFiniteTopZetaMismatch_ledger
    hε hSafe hZeta hArch hElem X
  rw [hledger]
  simp [pascalCenteredXiPrimeSideFiniteTopCompanion_eq_existing]
  ring

/-! ## CS29-H: scalar projection is weaker than a complex norm bound -/

theorem normalized_scalar_can_vanish_on_nonzero_complex :
    ∃ z : ℂ, z ≠ 0 ∧ (((2 * Real.pi * Complex.I)⁻¹) * z).re = 0 := by
  refine ⟨1, one_ne_zero, ?_⟩
  rw [normalized_by_two_pi_i_re]
  simp

theorem normalized_scalar_zero_with_unbounded_real_part
    (C : ℝ) :
    ∃ z : ℂ, C < z.re ∧ (((2 * Real.pi * Complex.I)⁻¹) * z).re = 0 := by
  refine ⟨((|C| + 1 : ℝ) : ℂ), ?_, ?_⟩
  · simp
    linarith [le_abs_self C]
  · rw [normalized_by_two_pi_i_re]
    simp

/-! ## CS29-I/J: structural closure only -/

inductive PascalCenteredXiPrimeSideFiniteScalarMismatchGap : Prop
  | no_independent_scalar_mismatch_estimate

end DkMath.RH.CFBRCProjection
