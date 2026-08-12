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
algebra, pole-free rectangle lemma, and strict-inside square geometry needed
for the XDP-013 micro-checkpoint.  The explicit complex square normalization
`∮ dz / z = 2 * π * I` is intentionally not axiomatized: it remains the
documented frontier when the pinned interval-integral normal forms do not
close the four complex side calculations.  No residue provider is introduced
under the guise of a theorem.
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
