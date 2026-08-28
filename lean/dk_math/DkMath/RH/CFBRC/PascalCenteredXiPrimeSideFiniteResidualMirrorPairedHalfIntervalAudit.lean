/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualIntervalLocalRegularityAudit
import Mathlib.Tactic

/-!
# CS35: mirror-paired finite residual on the centered top edge

This module compresses the already finite CS34 observable by the affine mirror
`u ↦ 1 - u`.  Every statement is pointwise or finite-interval local.  In
particular, this file does not add a sign estimate, a limiting prime expansion,
a limit exchange, or an RH conclusion.
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

private theorem cs35_star_re (z : ℂ) :
    (star z).re = z.re := by
  rw [Complex.star_def]
  simp

private theorem cs35_star_im (z : ℂ) :
    (star z).im = -z.im := by
  rw [Complex.star_def]
  simp

private theorem cs35_mul_im_pair (a b c : ℂ) :
    (a * b).im + (star a * c).im =
      (a * (b - star c)).im := by
  rw [Complex.mul_im, Complex.mul_im, Complex.mul_im,
    Complex.sub_re, Complex.sub_im]
  simp [Complex.conj_re, Complex.conj_im]; ring

private theorem cs35_mul_im_pair_mirror (a b c : ℂ) :
    (star a * (b - star c)).im =
      (a * (c - star b)).im := by
  rw [Complex.mul_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    ]
  simp [Complex.conj_re, Complex.conj_im]; ring

/-! ## CS35-A: centered top geometry and weight parity -/

theorem pascalCenteredXiPrimeSideFiniteResidualTopEdge_mirror
    (u T : ℝ) :
    pascalSymmetricRectangleTopEdge (1 - u) T =
      1 - starRingEnd ℂ (pascalSymmetricRectangleTopEdge u T) := by
  apply Complex.ext <;>
    simp [pascalSymmetricRectangleTopEdge]

theorem pascalCenteredXiPrimeSideFiniteResidualTopCentered_mirror
    (u T : ℝ) :
    pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge (1 - u) T) =
      -starRingEnd ℂ
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u T)) := by
  rw [pascalCenteredXiPrimeSideFiniteResidualTopEdge_mirror]
  have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    apply Complex.ext <;> norm_num
  simp only [pascalOrdinaryToCentered, criticalLineCenter, map_sub]
  rw [hhalf]
  ring

theorem pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror
    {W : PascalCenteredXiResidueTransportWindow}
    {u : ℝ} (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    1 - u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) := by
  have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  rw [Set.uIcc_of_ge hσ] at hu ⊢
  exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

private theorem pascalCenteredXiMellinQuadraticMultiplier_conj_cs35
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    mellinQuadraticBoxMultiplier ε (starRingEnd ℂ z) =
      starRingEnd ℂ (mellinQuadraticBoxMultiplier ε z) := by
  rw [mellinQuadraticBoxMultiplier_eq_logAverage hε,
    mellinQuadraticBoxMultiplier_eq_logAverage hε]
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
    simp only [map_ofNat]
  have hscale : starRingEnd ℂ ((2 * ε : ℝ)⁻¹ : ℂ) =
      ((2 * ε : ℝ)⁻¹ : ℂ) := by
    simp [map_inv₀, htwo, Complex.ofReal_mul]
  calc
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * starRingEnd ℂ z)) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε,
          starRingEnd ℂ (Complex.exp ((t : ℂ) * z))) := by
            congr 1
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with t ht
            rw [← Complex.exp_conj]
            congr 1
            simp
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        starRingEnd ℂ (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) := by
          rw [intervalIntegral.intervalIntegral_conj]
    _ = starRingEnd ℂ
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z))) := by
          rw [map_mul, hscale]

private theorem pascalCenteredXiMellinSecondDifferenceWeight_conj_cs35
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0 (starRingEnd ℂ z) =
      starRingEnd ℂ
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0 z) := by
  rw [pascalCenteredXiMellinQuadraticWeight_eq_generic hε,
    pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
  unfold mellinQuadraticBoxWeight
  rw [map_mul, map_pow, pascalCenteredXiMellinQuadraticMultiplier_conj_cs35 hε]

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_mirror
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W (1 - u) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u) := by
  unfold pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight
  rw [pascalCenteredXiPrimeSideFiniteResidualTopCentered_mirror,
    pascalCenteredXiMellinSecondDifferenceWeight_even hε,
    pascalCenteredXiMellinSecondDifferenceWeight_conj_cs35 hε]

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal_mirror
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W (1 - u) =
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal ε W u := by
  have h := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_mirror
    hε W u
  simpa [pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightReal,
    Complex.conj_re] using congrArg Complex.re h

theorem pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag_mirror
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W (1 - u) =
      -pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag ε W u := by
  have h := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_mirror
    hε W u
  have hi := congrArg Complex.im h
  simpa [pascalCenteredXiPrimeSideFiniteResidualTopMellinWeightImag,
    Complex.conj_im] using hi

/-! ## CS35-B: the mirror-paired finite residual -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorPair
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopPath X W u *
    starRingEnd ℂ (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 - u))

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_ne_zero
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u ≠ 0 := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorPair
  apply mul_ne_zero
  · exact pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero hSafe hu
  · intro h
    have h' := pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero
      (X := X) hSafe (pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror hu)
    apply h'
    simpa using h

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center
    {W : PascalCenteredXiResidueTransportWindow}
    (_hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W (1 / 2 : ℝ) =
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ)) := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorPair
  have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  change pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ) *
      star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W
        (1 / 2 : ℝ)) = _
  exact Complex.mul_conj _

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center_re_pos
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
    0 < (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W
      (1 / 2 : ℝ)).re := by
  rw [pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center hSafe]
  exact Complex.normSq_pos.mpr
    (pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero hSafe
      (by
        have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
          linarith [W.rectangle.hσ]
        rw [Set.uIcc_of_ge hσ]
        constructor <;> linarith [W.rectangle.hσ]))

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center_im
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
    (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W
      (1 / 2 : ℝ)).im = 0 := by
  rw [pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center hSafe]
  simp [Complex.normSq_apply]

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_mirror
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W (1 - u) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u) := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorPair
  simp only [sub_sub_cancel]
  rw [map_mul]
  simp only [starRingEnd_apply]
  change pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 - u) *
      star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u) =
    star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u) *
      star (star
        (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 - u)))
  rw [star_star]
  ring

/-! ## CS35-C/D: paired rate and scalar density -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorRate
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualLogRate X W u -
    starRingEnd ℂ (pascalCenteredXiPrimeSideFiniteResidualLogRate X W (1 - u))

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity
    (ε : ℝ) (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u).im

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorRate_channels
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    (pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u).re =
        pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u -
          pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W (1 - u) ∧
    (pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u).im =
        pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u +
          pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W (1 - u) := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorRate
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate
    pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate
  simp only [starRingEnd_apply, Complex.sub_re, Complex.sub_im]
  constructor <;> simp

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_hasDerivAt
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W)
      (-pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u *
        pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u) u := by
  have hmirror := pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror hu
  have hF := pascalCenteredXiPrimeSideFiniteResidualTopPath_hasDerivAt
    (X := X) hSafe hu
  have hFm := pascalCenteredXiPrimeSideFiniteResidualTopPath_hasDerivAt
    (X := X) hSafe hmirror
  have hcomp := hFm.comp_const_sub 1 u
  have hstar := hcomp.star
  have hprod := hF.mul hstar
  convert hprod using 1 <;> try rfl
  change
    -(pascalCenteredXiPrimeSideFiniteResidualLogRate X W u -
        starRingEnd ℂ
          (pascalCenteredXiPrimeSideFiniteResidualLogRate X W (1 - u))) *
        (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u *
          starRingEnd ℂ
            (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 - u))) =
      -pascalCenteredXiPrimeSideFiniteResidualLogRate X W u *
          pascalCenteredXiPrimeSideFiniteResidualTopPath X W u *
          starRingEnd ℂ
            (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 - u)) +
        pascalCenteredXiPrimeSideFiniteResidualTopPath X W u *
          starRingEnd ℂ
            (-(-pascalCenteredXiPrimeSideFiniteResidualLogRate X W (1 - u) *
              pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 - u)))
  simp only [map_neg, map_mul]
  ring

theorem pascalCenteredXiPrimeSideFiniteResidualScalarDensity_add_mirror
    {ε : ℝ} (hε : 0 < ε)
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W u +
        pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W (1 - u) =
      pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u := by
  let H : ℝ → ℂ := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W
  let q : ℝ → ℂ := pascalCenteredXiPrimeSideFiniteResidualLogRate X W
  change (H u * q u).im + (H (1 - u) * q (1 - u)).im =
    (H u * (q u - star (q (1 - u)))).im
  have hH : H (1 - u) = star (H u) := by
    dsimp [H]
    simpa only [starRingEnd_apply] using
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_mirror hε W u)
  rw [hH]
  exact cs35_mul_im_pair _ _ _

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_mirror
    {ε : ℝ} (hε : 0 < ε)
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W (1 - u) =
      pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u := by
  let H : ℝ → ℂ := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W
  let q : ℝ → ℂ := pascalCenteredXiPrimeSideFiniteResidualLogRate X W
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity
    pascalCenteredXiPrimeSideFiniteResidualMirrorRate
  simp only [sub_sub_cancel]
  change (H (1 - u) * (q (1 - u) - star (q u))).im =
    (H u * (q u - star (q (1 - u)))).im
  have hH : H (1 - u) = star (H u) := by
    dsimp [H]
    simpa only [starRingEnd_apply] using
      (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight_mirror hε W u)
  rw [hH]
  exact cs35_mul_im_pair_mirror _ _ _

/-! ## CS35-F: a canonical paired polar carrier -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorNormSq
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  Complex.normSq (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u)

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u /
    starRingEnd ℂ (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u)

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorNormSq_pos
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    0 < pascalCenteredXiPrimeSideFiniteResidualMirrorNormSq X W u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorNormSq
  exact Complex.normSq_pos.mpr
    (pascalCenteredXiPrimeSideFiniteResidualMirrorPair_ne_zero hSafe hu)

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier_center
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier X W (1 / 2 : ℝ) = 1 := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier
  rw [pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center hSafe]
  have hF : pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ) ≠ 0 :=
    pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero hSafe
      (by
        have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
          linarith [W.rectangle.hσ]
        rw [Set.uIcc_of_ge hσ]
        constructor <;> linarith [W.rectangle.hσ])
  have hn : (Complex.normSq
      (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hF).ne'
  have hstar : starRingEnd ℂ
      (Complex.normSq
        (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ))) =
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ)) := by
    apply Complex.ext <;> simp
  rw [hstar]
  exact (div_self hn)

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier_normSq
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    Complex.normSq
        (pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier X W u) = 1 := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseCarrier
  have hne := pascalCenteredXiPrimeSideFiniteResidualMirrorPair_ne_zero
    (X := X) hSafe hu
  have hn : Complex.normSq
      (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u) ≠ 0 :=
    (Complex.normSq_pos.mpr hne).ne'
  rw [Complex.normSq_div]
  rw [Complex.normSq_conj]
  field_simp [hn]

/-! ## CS35-E: orientation-safe integral compression -/

theorem intervalIntegral_eq_half_integral_add_mirror
    {ρ P : ℝ → ℝ} {a b : ℝ}
    (hab : 1 - b = a) (hba : 1 - a = b)
    (hρ : IntervalIntegrable ρ volume a b)
    (hρm : IntervalIntegrable (fun u => ρ (1 - u)) volume a b)
    (hpair : ∀ u, ρ u + ρ (1 - u) = P u) :
    (∫ u in a..b, ρ u) =
      (1 / 2 : ℝ) * ∫ u in a..b, P u := by
  have hmirror : (∫ u in a..b, ρ (1 - u)) = ∫ u in a..b, ρ u := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := ρ) (a := a) (b := b) (d := 1)
    simp [h, hab, hba]
  have hsum :
      (∫ u in a..b, (ρ u + ρ (1 - u))) =
        (∫ u in a..b, ρ u) + ∫ u in a..b, ρ (1 - u) := by
    rw [intervalIntegral.integral_add hρ hρm]
  have hsum' :
      (∫ u in a..b, P u) =
        2 * ∫ u in a..b, ρ u := by
    calc
      (∫ u in a..b, P u) =
          ∫ u in a..b, (ρ u + ρ (1 - u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        change P u = ρ u + ρ (1 - u)
        exact (hpair u).symm
      _ = (∫ u in a..b, ρ u) +
          ∫ u in a..b, ρ (1 - u) := hsum
      _ = 2 * ∫ u in a..b, ρ u := by rw [hmirror]; ring
  rw [hsum']
  ring

theorem intervalIntegral_mirror_even_eq_two_half_interval
    {P : ℝ → ℝ} {a b c : ℝ}
    (hab : 1 - b = a) (hc : 1 - c = c)
    (hPleft : IntervalIntegrable P volume a c)
    (hPright : IntervalIntegrable P volume c b)
    (heven : ∀ u, P (1 - u) = P u) :
    (∫ u in a..b, P u) = 2 * ∫ u in a..c, P u := by
  have hreflect :
      (∫ u in c..b, P (1 - u)) = ∫ u in a..c, P u := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := P) (a := c) (b := b) (d := 1)
    simp [h, hab, hc]
  have hright :
      (∫ u in c..b, P u) = ∫ u in a..c, P u := by
    calc
      (∫ u in c..b, P u) = ∫ u in c..b, P (1 - u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        change P u = P (1 - u)
        exact (heven u).symm
      _ = ∫ u in a..c, P u := hreflect
  have hsplit :
      (∫ u in a..b, P u) =
        (∫ u in a..c, P u) + ∫ u in c..b, P u := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals hPleft hPright
  rw [hsplit, hright]
  ring

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_integral_half_interval
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} (X : ℕ)
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
    (∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
      pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W u) =
      ∫ u in W.rectangle.σ..(1 / 2 : ℝ),
        pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u := by
  have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have havg := intervalIntegral_eq_half_integral_add_mirror
    (ρ := pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
    (P := pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
    (a := W.rectangle.σ) (b := 1 - W.rectangle.σ)
    (by ring) (by ring) hρ hρm
    (fun u => pascalCenteredXiPrimeSideFiniteResidualScalarDensity_add_mirror
      hε X W u)
  have hhalf := intervalIntegral_mirror_even_eq_two_half_interval
    (P := pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
    (a := W.rectangle.σ) (b := 1 - W.rectangle.σ) (c := (1 / 2 : ℝ))
    (by ring) (by norm_num) hPairLeft hPairRight
    (fun u => pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_mirror
      hε X W u)
  rw [havg, hhalf]
  ring

/-! ## CS35-F bonus: center-normalized notation -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorAmplitudeDisplacement
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..u,
    (pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W v).re

noncomputable def pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseDisplacement
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..u,
    (pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W v).im

@[simp] theorem pascalCenteredXiPrimeSideFiniteResidualMirrorAmplitudeDisplacement_center
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorAmplitudeDisplacement X W
      (1 / 2 : ℝ) = 0 := by
  simp [pascalCenteredXiPrimeSideFiniteResidualMirrorAmplitudeDisplacement]

@[simp] theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseDisplacement_center
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseDisplacement X W
      (1 / 2 : ℝ) = 0 := by
  simp [pascalCenteredXiPrimeSideFiniteResidualMirrorPhaseDisplacement]

end DkMath.RH.CFBRCProjection
