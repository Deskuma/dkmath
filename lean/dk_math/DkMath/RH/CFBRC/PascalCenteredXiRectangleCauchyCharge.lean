/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaRectangleResidueTransport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# One-pole Cauchy charge for finite rectangles

This module supplies the coordinate bridge, finite four-edge subdivision
algebra, pole-free rectangle lemma, strict-inside square geometry, and the
explicit square normalization `∮ dz / z = 2 * π * I` for XDP-013/XDP-014.
The normalization is proved by rational complex inverse identities, opposite
edge pairing, and the pinned real arctangent integral.  Its translated-square
companion is proved by four real interval translations.  No general residue,
winding, homotopy, or contour-deformation framework is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open Set
open scoped Interval Topology

/-! ## Gates 0/A: coordinate-safe pole bridge -/

/-- The ordinary location corresponding to a centered Xi zero. -/
def pascalCenteredXiOrdinaryPole (a : ℂ) : ℂ := pascalCenteredToOrdinary a

/-- Centered and ordinary pole coordinates differ by the canonical
ordinary-to-centered translation. -/
theorem pascalOrdinaryToCentered_sub_eq_sub_ordinaryPole (s a : ℂ) :
    pascalOrdinaryToCentered s - a =
      s - pascalCenteredXiOrdinaryPole a := by
  simp [pascalOrdinaryToCentered, pascalCenteredXiOrdinaryPole,
    pascalCenteredToOrdinary]
  ring

/-- A centered principal part pulled back to an ordinary rectangle is an
ordinary Cauchy kernel at the translated pole. -/
theorem pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel
    (h : ℂ → ℂ) (a s : ℂ) :
    pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered s) =
      (-(pascalCenteredXiZeroMultiplicity a : ℂ) * h a) *
        (s - pascalCenteredXiOrdinaryPole a)⁻¹ := by
  unfold pascalCenteredXiWeightedPrincipalPart
  rw [pascalOrdinaryToCentered_sub_eq_sub_ordinaryPole]

/-! ## Gate B: generic four-edge rectangle -/

/-- The positively oriented boundary integral of an axis-aligned rectangle,
written in the exact lower-left/upper-right form used by Mathlib. -/
noncomputable def pascalRectangleBoundaryIntegral
    (F : ℂ → ℂ) (xL xR yB yT : ℝ) : ℂ :=
  (∫ x in xL..xR, F (x + yB * Complex.I)) -
    (∫ x in xL..xR, F (x + yT * Complex.I)) +
    Complex.I • (∫ y in yB..yT, F (xR + y * Complex.I)) -
    Complex.I • (∫ y in yB..yT, F (xL + y * Complex.I))

/-- The generic boundary is Mathlib's rectangle boundary expression. -/
theorem pascalRectangleBoundaryIntegral_eq_mathlibBoundary
    (F : ℂ → ℂ) (xL xR yB yT : ℝ) :
    pascalRectangleBoundaryIntegral F xL xR yB yT =
      (∫ x in xL..xR, F (x + yB * Complex.I)) -
      (∫ x in xL..xR, F (x + yT * Complex.I)) +
      Complex.I • (∫ y in yB..yT, F (xR + y * Complex.I)) -
      Complex.I • (∫ y in yB..yT, F (xL + y * Complex.I)) := by
  rfl

/-- The generic boundary specializes to XDP-009's symmetric boundary. -/
theorem pascalRectangleBoundaryIntegral_symmetric
    (F : ℂ → ℂ) (σ T : ℝ) :
    pascalRectangleBoundaryIntegral F (1 - σ) σ (-T) T =
      pascalSymmetricRectangleBoundaryIntegral F σ T := by
  unfold pascalRectangleBoundaryIntegral
  rw [pascalSymmetricRectangleBoundaryIntegral_eq_mathlibBoundary]
  simp only [pascalSymmetricRectangleRightEdge,
    pascalSymmetricRectangleLeftEdge, pascalSymmetricRectangleTopEdge,
    pascalSymmetricRectangleBottomEdge, Complex.ofReal_neg, neg_mul,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  congr 1

/-! ## Gate C: finite subdivision algebra -/

/-- Vertical subdivision, with the interval-integrability hypotheses required
by the pinned interval-integral additivity theorem. -/
theorem pascalRectangleBoundaryIntegral_vertical_split
    (F : ℂ → ℂ) {xL c xR yB yT : ℝ}
    (hb₁ : IntervalIntegrable (fun x => F (x + yB * Complex.I)) volume xL c)
    (hb₂ : IntervalIntegrable (fun x => F (x + yB * Complex.I)) volume c xR)
    (ht₁ : IntervalIntegrable (fun x => F (x + yT * Complex.I)) volume xL c)
    (ht₂ : IntervalIntegrable (fun x => F (x + yT * Complex.I)) volume c xR)
    (_hv : IntervalIntegrable (fun y => F (c + y * Complex.I)) volume yB yT) :
    pascalRectangleBoundaryIntegral F xL xR yB yT =
      pascalRectangleBoundaryIntegral F xL c yB yT +
        pascalRectangleBoundaryIntegral F c xR yB yT := by
  have hb := intervalIntegral.integral_add_adjacent_intervals hb₁ hb₂
  have ht := intervalIntegral.integral_add_adjacent_intervals ht₁ ht₂
  unfold pascalRectangleBoundaryIntegral
  simp only [← hb, ← ht]
  simp [smul_eq_mul]
  ring

/-- Horizontal subdivision, with finite interval-integral additivity on the
two vertical sides. -/
theorem pascalRectangleBoundaryIntegral_horizontal_split
    (F : ℂ → ℂ) {xL xR yB d yT : ℝ}
    (_hb : IntervalIntegrable (fun x => F (x + yB * Complex.I)) volume xL xR)
    (_ht : IntervalIntegrable (fun x => F (x + yT * Complex.I)) volume xL xR)
    (vr₁ : IntervalIntegrable (fun y => F (xR + y * Complex.I)) volume yB d)
    (vr₂ : IntervalIntegrable (fun y => F (xR + y * Complex.I)) volume d yT)
    (vl₁ : IntervalIntegrable (fun y => F (xL + y * Complex.I)) volume yB d)
    (vl₂ : IntervalIntegrable (fun y => F (xL + y * Complex.I)) volume d yT) :
    pascalRectangleBoundaryIntegral F xL xR yB yT =
      pascalRectangleBoundaryIntegral F xL xR yB d +
        pascalRectangleBoundaryIntegral F xL xR d yT := by
  have hvr := intervalIntegral.integral_add_adjacent_intervals vr₁ vr₂
  have hvl := intervalIntegral.integral_add_adjacent_intervals vl₁ vl₂
  unfold pascalRectangleBoundaryIntegral
  simp only [← hvr, ← hvl]
  simp [smul_eq_mul]
  ring

/-! ## Gate D: strict-inside square geometry -/

/-- A square with four positive side margins lies in the corresponding
closed rectangle. -/
theorem pascalRectangle_square_subset_open
    {xL xR yB yT : ℝ} {p : ℂ} {δ : ℝ}
    (hδ : 0 < δ)
    (hxL : xL < p.re - δ) (hxR : p.re + δ < xR)
    (hyB : yB < p.im - δ) (hyT : p.im + δ < yT) :
    Set.Icc (p.re - δ) (p.re + δ) ×ℂ Set.Icc (p.im - δ) (p.im + δ) ⊆
      Set.uIcc xL xR ×ℂ Set.uIcc yB yT := by
  intro z hz
  rcases hz with ⟨⟨hzxL, hzxR⟩, ⟨hzyB, hzyT⟩⟩
  have hx : xL ≤ xR := by linarith
  have hy : yB ≤ yT := by linarith
  rw [uIcc_of_le hx, uIcc_of_le hy]
  exact ⟨⟨le_trans (le_of_lt hxL) hzxL, le_trans hzxR hxR.le⟩,
    ⟨le_trans (le_of_lt hyB) hzyB, le_trans hzyT hyT.le⟩⟩

/-- Every point in an open rectangle has a strictly positive square radius
whose closed square remains inside it. -/
theorem exists_pascalRectangle_square_radius
    {xL xR yB yT : ℝ} {p : ℂ}
    (hp : p ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT) :
    ∃ δ : ℝ, 0 < δ ∧ xL < p.re - δ ∧ p.re + δ < xR ∧
      yB < p.im - δ ∧ p.im + δ < yT := by
  rcases hp with ⟨⟨hpxL, hpxR⟩, ⟨hpyB, hpyT⟩⟩
  let δ : ℝ := min (min (p.re - xL) (xR - p.re))
    (min (p.im - yB) (yT - p.im)) / 2
  have h₁ : 0 < p.re - xL := sub_pos.mpr hpxL
  have h₂ : 0 < xR - p.re := sub_pos.mpr hpxR
  have h₃ : 0 < p.im - yB := sub_pos.mpr hpyB
  have h₄ : 0 < yT - p.im := sub_pos.mpr hpyT
  have hmin : 0 < min (min (p.re - xL) (xR - p.re))
      (min (p.im - yB) (yT - p.im)) := by positivity
  have hmL : min (min (p.re - xL) (xR - p.re))
      (min (p.im - yB) (yT - p.im)) ≤ p.re - xL :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hmR : min (min (p.re - xL) (xR - p.re))
      (min (p.im - yB) (yT - p.im)) ≤ xR - p.re :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hmB : min (min (p.re - xL) (xR - p.re))
      (min (p.im - yB) (yT - p.im)) ≤ p.im - yB :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hmT : min (min (p.re - xL) (xR - p.re))
      (min (p.im - yB) (yT - p.im)) ≤ yT - p.im :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, by dsimp [δ]; linarith, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [δ] <;> linarith

/-! ## Gate C/D: real scalar normalization -/

/-- The real integral occurring after pairing opposite sides of a centered
square.  This is the pinned `integral_inv_sq_add_sq` theorem specialized to
the symmetric interval `[-δ, δ]`, with the arctangent values normalized. -/
theorem integral_inv_sq_add_sq_neg_delta_delta
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in (-δ)..δ, (t ^ 2 + δ ^ 2)⁻¹) =
      Real.pi / (2 * δ) := by
  calc
    (∫ t in (-δ)..δ, (t ^ 2 + δ ^ 2)⁻¹) =
        δ⁻¹ * (Real.arctan (δ / δ) - Real.arctan (-δ / δ)) := by
      have hfun : (fun t : ℝ => (t ^ 2 + δ ^ 2)⁻¹) =
          (fun t : ℝ => (δ ^ 2 + t ^ 2)⁻¹) := by
        funext t
        congr 1
        ring
      rw [hfun]
      exact integral_inv_sq_add_sq (a := -δ) (b := δ) hδ.ne'
    _ = Real.pi / (2 * δ) := by
      rw [div_self hδ.ne', neg_div, div_self hδ.ne']
      rw [Real.arctan_one, Real.arctan_neg, Real.arctan_one]
      field_simp
      ring

/-- Pointwise bottom/top pairing for the inverse on a centered square. -/
theorem pascalSquare_inv_bottom_top_pointwise
    {δ x : ℝ} (hδ : 0 < δ) :
    ((x : ℂ) - δ * Complex.I)⁻¹ - ((x : ℂ) + δ * Complex.I)⁻¹ =
      (2 * δ * Complex.I) * (((x ^ 2 + δ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hden : x ^ 2 + δ ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x, sq_nonneg δ]
  have hdenC : ((x ^ 2 + δ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hminus : (x : ℂ) - δ * Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hplus : (x : ℂ) + δ * Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [Complex.ofReal_inv]
  field_simp [hminus, hplus, hden, hdenC]
  ring_nf
  simp [Complex.ofReal_pow]
  ring

/-- The paired bottom/top interval is the constant imaginary factor times the
real scalar integral used in the square normalization. -/
theorem pascalSquare_inv_bottom_top_integral
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in (-δ)..δ, ((x : ℂ) - δ * Complex.I)⁻¹) -
        (∫ x in (-δ)..δ, ((x : ℂ) + δ * Complex.I)⁻¹) =
      (2 * δ * Complex.I) *
        (((∫ x in (-δ)..δ, (x ^ 2 + δ ^ 2)⁻¹) : ℝ) : ℂ) := by
  have hminus : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) - δ * Complex.I)⁻¹) volume (-δ) δ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx hzero
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  have hplus : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + δ * Complex.I)⁻¹) volume (-δ) δ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx hzero
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  rw [← intervalIntegral.integral_sub hminus hplus]
  rw [intervalIntegral.integral_congr (fun x hx =>
    pascalSquare_inv_bottom_top_pointwise hδ)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

/-- Pointwise right/left pairing, including the positive-orientation factor
`I` carried by the vertical edges. -/
theorem pascalSquare_inv_right_left_pointwise
    {δ y : ℝ} (hδ : 0 < δ) :
    Complex.I * ((δ : ℂ) + y * Complex.I)⁻¹ -
        Complex.I * ((-δ : ℂ) + y * Complex.I)⁻¹ =
      (2 * δ * Complex.I) * (((y ^ 2 + δ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hden : y ^ 2 + δ ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg y, sq_nonneg δ]
  have hdenC : ((y ^ 2 + δ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hright : (δ : ℂ) + y * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hleft : (-δ : ℂ) + y * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hright' : (δ : ℂ) + Complex.I * y ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hleft' : (-δ : ℂ) + Complex.I * y ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [Complex.ofReal_inv]
  field_simp [hright, hleft, hright', hleft', hden, hdenC]
  ring_nf
  simp [Complex.ofReal_pow]
  ring

/-- The unweighted right/left inverse difference used before applying the
vertical-edge orientation factor. -/
theorem pascalSquare_inv_right_left_unweighted_pointwise
    {δ y : ℝ} (hδ : 0 < δ) :
    ((δ : ℂ) + y * Complex.I)⁻¹ - ((-δ : ℂ) + y * Complex.I)⁻¹ =
      (2 * δ) * (((y ^ 2 + δ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h := pascalSquare_inv_right_left_pointwise (y := y) hδ
  apply (mul_left_cancel₀ (by simp : Complex.I ≠ 0))
  calc
    Complex.I * (((δ : ℂ) + y * Complex.I)⁻¹ -
        ((-δ : ℂ) + y * Complex.I)⁻¹) =
        Complex.I * ((δ : ℂ) + y * Complex.I)⁻¹ -
          Complex.I * ((-δ : ℂ) + y * Complex.I)⁻¹ := by ring
    _ = (2 * δ * Complex.I) * (((y ^ 2 + δ ^ 2)⁻¹ : ℝ) : ℂ) := h
    _ = Complex.I * ((2 * δ) * (((y ^ 2 + δ ^ 2)⁻¹ : ℝ) : ℂ)) := by ring

/-- The paired right/left interval is the same constant imaginary factor
as the bottom/top pair. -/
theorem pascalSquare_inv_right_left_integral
    {δ : ℝ} (hδ : 0 < δ) :
    Complex.I • (∫ y in (-δ)..δ, ((δ : ℂ) + y * Complex.I)⁻¹) -
        Complex.I • (∫ y in (-δ)..δ, ((-δ : ℂ) + y * Complex.I)⁻¹) =
      (2 * δ * Complex.I) *
        (((∫ y in (-δ)..δ, (y ^ 2 + δ ^ 2)⁻¹) : ℝ) : ℂ) := by
  have hright : IntervalIntegrable
      (fun y : ℝ => ((δ : ℂ) + y * Complex.I)⁻¹) volume (-δ) δ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro y hy hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
  have hleft : IntervalIntegrable
      (fun y : ℝ => ((-δ : ℂ) + y * Complex.I)⁻¹) volume (-δ) δ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro y hy hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
  rw [smul_eq_mul, smul_eq_mul]
  rw [← mul_sub, ← intervalIntegral.integral_sub hright hleft]
  rw [intervalIntegral.integral_congr (fun y hy =>
    pascalSquare_inv_right_left_unweighted_pointwise hδ)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  ring

/-- The principal square normalization: the positively oriented boundary
integral of the totalized inverse around a square centered at the origin is
`2 * π * I`. -/
theorem pascalRectangleBoundaryIntegral_inv_centeredSquare
    {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => z⁻¹)
      (-δ) δ (-δ) δ = 2 * Real.pi * Complex.I := by
  unfold pascalRectangleBoundaryIntegral
  simp only [Complex.ofReal_neg]
  simp only [neg_mul, ← sub_eq_add_neg]
  change
    ((∫ x in (-δ)..δ, ((x : ℂ) - δ * Complex.I)⁻¹) -
        (∫ x in (-δ)..δ, ((x : ℂ) + δ * Complex.I)⁻¹)) +
      Complex.I • (∫ y in (-δ)..δ, ((δ : ℂ) + y * Complex.I)⁻¹) -
      Complex.I • (∫ y in (-δ)..δ, ((-δ : ℂ) + y * Complex.I)⁻¹) =
    2 * Real.pi * Complex.I
  rw [pascalSquare_inv_bottom_top_integral hδ]
  rw [add_sub_assoc]
  rw [pascalSquare_inv_right_left_integral hδ]
  rw [integral_inv_sq_add_sq_neg_delta_delta hδ]
  field_simp [hδ.ne']
  norm_num [Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hδ.ne']

/-- Translation of the square normalization to an arbitrary complex pole.
The proof uses only the four real interval translation identities; no general
contour-translation or residue framework is introduced. -/
theorem pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare
    {p : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      (p.re - δ) (p.re + δ) (p.im - δ) (p.im + δ) =
      2 * Real.pi * Complex.I := by
  unfold pascalRectangleBoundaryIntegral
  simp only [Complex.ofReal_sub, Complex.ofReal_add]
  have hbottom :
      (∫ x in (p.re - δ)..(p.re + δ),
        ((x : ℂ) + (p.im - δ) * Complex.I - p)⁻¹) =
      ∫ x in (-δ)..δ, ((x : ℂ) - δ * Complex.I)⁻¹ := by
    have hfun : (fun x : ℝ =>
        ((x : ℂ) + (p.im - δ) * Complex.I - p)⁻¹) =
        (fun x : ℝ => (((x - p.re : ℝ) : ℂ) - δ * Complex.I)⁻¹) := by
      funext x
      apply congrArg (fun z : ℂ => z⁻¹)
      apply Complex.ext <;> simp
    rw [hfun]
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun x : ℝ => ((x : ℂ) - δ * Complex.I)⁻¹)
      (a := p.re - δ) (b := p.re + δ) p.re
    simpa using h
  have htop :
      (∫ x in (p.re - δ)..(p.re + δ),
        ((x : ℂ) + (p.im + δ) * Complex.I - p)⁻¹) =
      ∫ x in (-δ)..δ, ((x : ℂ) + δ * Complex.I)⁻¹ := by
    have hfun : (fun x : ℝ =>
        ((x : ℂ) + (p.im + δ) * Complex.I - p)⁻¹) =
        (fun x : ℝ => (((x - p.re : ℝ) : ℂ) + δ * Complex.I)⁻¹) := by
      funext x
      apply congrArg (fun z : ℂ => z⁻¹)
      apply Complex.ext <;> simp
    rw [hfun]
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun x : ℝ => ((x : ℂ) + δ * Complex.I)⁻¹)
      (a := p.re - δ) (b := p.re + δ) p.re
    simpa using h
  have hright :
      (∫ y in (p.im - δ)..(p.im + δ),
        ((p.re + δ : ℂ) + y * Complex.I - p)⁻¹) =
      ∫ y in (-δ)..δ, ((δ : ℂ) + y * Complex.I)⁻¹ := by
    have hfun : (fun y : ℝ =>
        ((p.re + δ : ℂ) + y * Complex.I - p)⁻¹) =
        (fun y : ℝ => ((δ : ℂ) + (y - p.im) * Complex.I)⁻¹) := by
      funext y
      apply congrArg (fun z : ℂ => z⁻¹)
      apply Complex.ext <;> simp
    rw [hfun]
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => ((δ : ℂ) + y * Complex.I)⁻¹)
      (a := p.im - δ) (b := p.im + δ) p.im
    simpa using h
  have hleft :
      (∫ y in (p.im - δ)..(p.im + δ),
        ((p.re - δ : ℂ) + y * Complex.I - p)⁻¹) =
      ∫ y in (-δ)..δ, ((-δ : ℂ) + y * Complex.I)⁻¹ := by
    have hfun : (fun y : ℝ =>
        ((p.re - δ : ℂ) + y * Complex.I - p)⁻¹) =
        (fun y : ℝ => ((-δ : ℂ) + (y - p.im) * Complex.I)⁻¹) := by
      funext y
      apply congrArg (fun z : ℂ => z⁻¹)
      apply Complex.ext <;> simp
    rw [hfun]
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => ((-δ : ℂ) + y * Complex.I)⁻¹)
      (a := p.im - δ) (b := p.im + δ) p.im
    simpa using h
  rw [hbottom, htop, hright, hleft]
  simpa only [pascalRectangleBoundaryIntegral, Complex.ofReal_neg, neg_mul,
    ← sub_eq_add_neg] using
    (pascalRectangleBoundaryIntegral_inv_centeredSquare (δ := δ) hδ)

/-! ## Gate E1: pole-free rectangle -/

/-- The ordinary Cauchy kernel has zero boundary integral when its pole is
outside the closed rectangle. -/
theorem pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed
    {xL xR yB yT : ℝ} (hx : xL ≤ xR) (hy : yB ≤ yT) {p : ℂ}
    (hp : p ∉ Set.uIcc xL xR ×ℂ Set.uIcc yB yT) :
    pascalRectangleBoundaryIntegral (fun s : ℂ => (s - p)⁻¹)
      xL xR yB yT = 0 := by
  have hne : ∀ z ∈ Set.uIcc xL xR ×ℂ Set.uIcc yB yT, z - p ≠ 0 := by
    intro z hz hzero
    apply hp
    exact (sub_eq_zero.mp hzero) ▸ hz
  have hclosed : ContinuousOn (fun s : ℂ => (s - p)⁻¹)
      (Set.uIcc xL xR ×ℂ Set.uIcc yB yT) := by
    intro z hz
    have hsub : DifferentiableAt ℂ (fun s : ℂ => s - p) z := by fun_prop
    exact (hsub.inv (hne z hz)).continuousAt.continuousWithinAt
  have hdiff : ∀ z ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT,
      DifferentiableAt ℂ (fun s : ℂ => (s - p)⁻¹) z := by
    intro z hz
    have hzclosed : z ∈ Set.uIcc xL xR ×ℂ Set.uIcc yB yT := by
      rw [Set.uIcc_of_le hx, Set.uIcc_of_le hy]
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
    have hsub : DifferentiableAt ℂ (fun s : ℂ => s - p) z := by fun_prop
    exact hsub.inv (hne z hzclosed)
  have hmath :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (fun s : ℂ => (s - p)⁻¹)
      ((xL : ℂ) + yB * Complex.I) ((xR : ℂ) + yT * Complex.I)
      (by simpa [Set.uIcc_of_le hx, Set.uIcc_of_le hy] using hclosed)
      (by
        intro z hz
        have hz' : z ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT := by
          simpa [Complex.add_re, Complex.add_im, min_eq_left hx,
            max_eq_right hx, min_eq_left hy, max_eq_right hy] using hz
        exact (hdiff z hz').differentiableWithinAt)
  simpa [pascalRectangleBoundaryIntegral, smul_eq_mul] using hmath

end DkMath.RH.CFBRCProjection
