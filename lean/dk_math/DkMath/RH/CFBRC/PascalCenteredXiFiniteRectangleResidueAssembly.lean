/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiRectangleCauchyCharge
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
import Mathlib.Tactic

/-!
# Finite rectangle principal-part and fixed-Xi residue assembly

This module closes the finite-sum part of XDP-016.  It proves rectangle
boundary linearity with explicit interval-integrability hypotheses, transports
the finite Xi principal parts through the ordinary-coordinate rectangle, and
assembles the raw regularizer with the principal-part sum.  All contours stay
at finite height.  No deformation, limiting argument, prime cutoff exchange,
defect-vanishing statement, or RH consequence is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open Set
open scoped Interval Topology

/-! ## Gate A: finite boundary linearity -/

/-- The four-edge symmetric rectangle integral is additive when both summands
are supplied with their oriented-edge interval-integrability contracts. -/
theorem pascalSymmetricRectangleBoundaryIntegral_add
    (F G : ℂ → ℂ)
    (hF : PascalSymmetricRectangleBoundaryIntegrable F σ T)
    (hG : PascalSymmetricRectangleBoundaryIntegrable G σ T) :
    pascalSymmetricRectangleBoundaryIntegral (fun z => F z + G z) σ T =
      pascalSymmetricRectangleBoundaryIntegral F σ T +
        pascalSymmetricRectangleBoundaryIntegral G σ T := by
  rcases hF with ⟨hFr, hFt, hFl, hFb⟩
  rcases hG with ⟨hGr, hGt, hGl, hGb⟩
  unfold pascalSymmetricRectangleBoundaryIntegral
  simp only [add_mul]
  rw [intervalIntegral.integral_add hFr hGr,
    intervalIntegral.integral_add hFt hGt,
    intervalIntegral.integral_add hFl hGl,
    intervalIntegral.integral_add hFb hGb]
  ring

/-- The oriented-edge integrability contract is additive. -/
theorem pascalSymmetricRectangleBoundaryIntegrable_add
    (F G : ℂ → ℂ)
    (hF : PascalSymmetricRectangleBoundaryIntegrable F σ T)
    (hG : PascalSymmetricRectangleBoundaryIntegrable G σ T) :
    PascalSymmetricRectangleBoundaryIntegrable (fun z => F z + G z) σ T := by
  rcases hF with ⟨hFr, hFt, hFl, hFb⟩
  rcases hG with ⟨hGr, hGt, hGl, hGb⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [add_mul] using hFr.add hGr
  · exact hFt.add hGt
  · simpa only [add_mul] using hFl.add hGl
  · exact hFb.add hGb

/-- The oriented-edge integrability contract is preserved by a finite sum. -/
theorem pascalSymmetricRectangleBoundaryIntegrable_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (σ T : ℝ)
    (hF : ∀ i ∈ s,
      PascalSymmetricRectangleBoundaryIntegrable (F i) σ T) :
    PascalSymmetricRectangleBoundaryIntegrable (fun z => ∑ i ∈ s, F i z) σ T := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [PascalSymmetricRectangleBoundaryIntegrable]
  | @insert i s hi ih =>
      have hiF := hF i (by simp)
      have hsF : ∀ j ∈ s,
          PascalSymmetricRectangleBoundaryIntegrable (F j) σ T := by
        intro j hj
        exact hF j (by simp [hj])
      have hsum := ih hsF
      have hadd := pascalSymmetricRectangleBoundaryIntegrable_add
        (F i) (fun z => ∑ j ∈ s, F j z) hiF hsum
      simpa only [Finset.sum_insert hi] using hadd

/-- A finite sum of rectangle-boundary integrals equals the boundary integral
of the finite sum, provided every summand has all four edge contracts. -/
theorem pascalSymmetricRectangleBoundaryIntegral_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (σ T : ℝ)
    (hF : ∀ i ∈ s,
      PascalSymmetricRectangleBoundaryIntegrable (F i) σ T) :
    pascalSymmetricRectangleBoundaryIntegral (fun z => ∑ i ∈ s, F i z) σ T =
      ∑ i ∈ s, pascalSymmetricRectangleBoundaryIntegral (F i) σ T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pascalSymmetricRectangleBoundaryIntegral]
  | @insert i s hi ih =>
      have hiF := hF i (by simp)
      have hsF : ∀ j ∈ s,
          PascalSymmetricRectangleBoundaryIntegrable (F j) σ T := by
        intro j hj
        exact hF j (by simp [hj])
      have ih' := ih hsF
      have hsumInt := pascalSymmetricRectangleBoundaryIntegrable_finset_sum s
        F σ T hsF
      have hsum :
          (fun z => ∑ j ∈ insert i s, F j z) =
            (fun z => F i z + ∑ j ∈ s, F j z) := by
        funext z
        rw [Finset.sum_insert hi]
      rw [hsum]
      rw [pascalSymmetricRectangleBoundaryIntegral_add (F i)
        (fun z => ∑ j ∈ s, F j z) hiF hsumInt]
      rw [ih']
      simp [Finset.sum_insert hi]

/-! ## Gate B: one principal part -/

/-- The coordinate-safe one-pole principal part is integrable on every
oriented edge of the fixed symmetric rectangle.  The proof uses the ordinary
pole localization from XDP-015 and the Cauchy-kernel edge helpers there. -/
theorem pascalCenteredXiRectangleBoundaryIntegrable_weightedPrincipalPart
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) {a : ℂ}
    (ha : a ∈ pascalCenteredXiZeroDiskFinset W.R) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T := by
  let p : ℂ := pascalCenteredXiOrdinaryPole a
  have hp : p ∈ pascalSymmetricRectangleOpen W.rectangle.σ W.rectangle.T := by
    exact pascalCenteredXiOrdinaryPole_mem_rectangleOpen_of_mem_zeroDiskFinset W ha
  rcases hp with ⟨⟨hpL, hpR⟩, ⟨hpB, hpT⟩⟩
  have hpre : p.re ≠ W.rectangle.σ := by linarith
  have hple : p.re ≠ 1 - W.rectangle.σ := by linarith
  have hpimB : p.im ≠ -W.rectangle.T := by linarith
  have hpimT : p.im ≠ W.rectangle.T := by linarith
  let c : ℂ := -(pascalCenteredXiZeroMultiplicity a : ℂ) * h a
  have hcoord : ∀ s : ℂ,
      pascalCenteredXiWeightedPrincipalPart h a
          (pascalOrdinaryToCentered s) = c * (s - p)⁻¹ := by
    intro s
    simpa [c, p] using
      pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel h a s
  have hrightKernel :
      IntervalIntegrable
        (fun t : ℝ => ((W.rectangle.σ : ℂ) + t * Complex.I - p)⁻¹)
        volume (-W.rectangle.T) W.rectangle.T := by
    simpa [pascalSymmetricRectangleRightEdge] using
      (intervalIntegrable_cauchyKernel_vertical_of_re_ne
        (p := p) (x := W.rectangle.σ) (a := -W.rectangle.T)
        (b := W.rectangle.T) hpre)
  have hleftKernel :
      IntervalIntegrable
        (fun t : ℝ => (((1 - W.rectangle.σ : ℝ) : ℂ) + t * Complex.I - p)⁻¹)
        volume (-W.rectangle.T) W.rectangle.T := by
    simpa [pascalSymmetricRectangleLeftEdge] using
      (intervalIntegrable_cauchyKernel_vertical_of_re_ne
        (p := p) (x := 1 - W.rectangle.σ) (a := -W.rectangle.T)
        (b := W.rectangle.T) hple)
  have htopKernel :
      IntervalIntegrable
        (fun u : ℝ => ((u : ℂ) + (W.rectangle.T : ℂ) * Complex.I - p)⁻¹)
        volume (1 - W.rectangle.σ) W.rectangle.σ := by
    simpa [pascalSymmetricRectangleTopEdge] using
      (intervalIntegrable_cauchyKernel_horizontal_of_im_ne
        (p := p) (y := W.rectangle.T) (a := 1 - W.rectangle.σ)
        (b := W.rectangle.σ) hpimT)
  have hbottomKernel :
      IntervalIntegrable
        (fun u : ℝ => ((u : ℂ) + ((-W.rectangle.T : ℝ) : ℂ) * Complex.I - p)⁻¹)
        volume (1 - W.rectangle.σ) W.rectangle.σ := by
    simpa [pascalSymmetricRectangleBottomEdge] using
      (intervalIntegrable_cauchyKernel_horizontal_of_im_ne
        (p := p) (y := -W.rectangle.T) (a := 1 - W.rectangle.σ)
        (b := W.rectangle.σ) hpimB)
  have hright : IntervalIntegrable
      (fun t : ℝ => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) * Complex.I)
      volume (-W.rectangle.T) W.rectangle.T := by
    have hc := hrightKernel.const_mul c
    have hc' : IntervalIntegrable
        (fun t : ℝ => pascalCenteredXiWeightedPrincipalPart h a
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)))
        volume (-W.rectangle.T) W.rectangle.T := by
      apply hc.congr
      intro t ht
      exact (hcoord (pascalSymmetricRectangleRightEdge W.rectangle.σ t)).symm
    exact hc'.mul_const Complex.I
  have hleft : IntervalIntegrable
      (fun t : ℝ => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleLeftEdge W.rectangle.σ t)) * Complex.I)
      volume W.rectangle.T (-W.rectangle.T) := by
    have hc := (hleftKernel.const_mul c).congr (fun t ht =>
      (hcoord (pascalSymmetricRectangleLeftEdge W.rectangle.σ t)).symm)
    exact hc.symm.mul_const Complex.I
  have htop : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)))
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
    have hc := (htopKernel.const_mul c).congr (fun u hu =>
      (hcoord (pascalSymmetricRectangleTopEdge u W.rectangle.T)).symm)
    exact hc.symm
  have hbottom : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleBottomEdge u W.rectangle.T)))
      volume (1 - W.rectangle.σ) W.rectangle.σ := by
    have hc : IntervalIntegrable
        (fun u : ℝ => pascalCenteredXiWeightedPrincipalPart h a
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleBottomEdge u W.rectangle.T)))
        volume (1 - W.rectangle.σ) W.rectangle.σ := by
      apply (hbottomKernel.const_mul c).congr
      intro u hu
      change c * ((u : ℂ) + ((-W.rectangle.T : ℝ) : ℂ) * Complex.I - p)⁻¹ =
        pascalCenteredXiWeightedPrincipalPart h a
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleBottomEdge u W.rectangle.T))
      rw [hcoord]
      simp only [pascalSymmetricRectangleBottomEdge]
      push_cast
      ring
    exact hc
  exact ⟨hright, htop, hleft, hbottom⟩

/-! ## Gate C: finite principal-part sum -/

/-- The finite disk principal-part sum is interval-integrable on every edge
of the ordinary rectangle after the canonical centered-coordinate pullback. -/
theorem pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedPrincipalPartSum
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T := by
  apply pascalSymmetricRectangleBoundaryIntegrable_finset_sum
  intro a ha
  exact pascalCenteredXiRectangleBoundaryIntegrable_weightedPrincipalPart h W ha

/-- The finite rectangle charge of the principal-part sum is the finite
weighted Xi zero moment with the Cauchy normalization and orientation sign. -/
theorem pascalCenteredXiRectangleIntegral_diskWeightedPrincipalPartSum_eq
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalSymmetricRectangleBoundaryIntegral
      (fun s => pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R := by
  let S := pascalCenteredXiZeroDiskFinset W.R
  let P : ℂ → ℂ → ℂ := fun a s =>
    pascalCenteredXiWeightedPrincipalPart h a
      (pascalOrdinaryToCentered s)
  have hsum := pascalSymmetricRectangleBoundaryIntegral_finset_sum
    S P W.rectangle.σ W.rectangle.T (by
      intro a ha
      simpa [P, S] using
        pascalCenteredXiRectangleBoundaryIntegrable_weightedPrincipalPart h W ha)
  rw [show (fun s => pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
      (pascalOrdinaryToCentered s)) = (fun s => ∑ a ∈ S, P a s) by
        funext s
        rfl]
  rw [hsum]
  have hterms :
      (∑ a ∈ S, pascalSymmetricRectangleBoundaryIntegral (P a)
          W.rectangle.σ W.rectangle.T) =
        ∑ a ∈ S, (-(2 * Real.pi * Complex.I) *
          (pascalCenteredXiZeroMultiplicity a : ℂ) * h a) := by
    apply Finset.sum_congr rfl
    intro a ha
    simpa [P, S] using
      (exists_pascalCenteredXiRectanglePrincipalPartChargeProvider h W).principalPart_boundary_eq
        (a := a) ha
  rw [hterms]
  unfold pascalCenteredXiZeroDiskWeightedMoment
  dsimp [S]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

/-! ## Gate D: raw regularizer boundary integrability -/

/-- Every parameterized edge of the finite rectangle is contained in the
closed rectangle seen by the patched-regularizer continuity theorem. -/
theorem pascalCenteredXiRectangle_edge_mem_closed
    (W : PascalCenteredXiResidueTransportWindow) :
    (∀ t : ℝ, t ∈ Set.uIcc (-W.rectangle.T) W.rectangle.T →
      pascalSymmetricRectangleRightEdge W.rectangle.σ t ∈
        pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) ∧
    (∀ t : ℝ, t ∈ Set.uIcc (-W.rectangle.T) W.rectangle.T →
      pascalSymmetricRectangleLeftEdge W.rectangle.σ t ∈
        pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) ∧
    (∀ u : ℝ, u ∈ Set.uIcc (1 - W.rectangle.σ) W.rectangle.σ →
      pascalSymmetricRectangleTopEdge u W.rectangle.T ∈
        pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) ∧
    (∀ u : ℝ, u ∈ Set.uIcc (1 - W.rectangle.σ) W.rectangle.σ →
      pascalSymmetricRectangleBottomEdge u W.rectangle.T ∈
        pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) := by
  have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have hT : -W.rectangle.T ≤ W.rectangle.T := by
    linarith [W.rectangle.hT]
  rw [pascalSymmetricRectangleClosed]
  rw [Set.uIcc_of_le hσ, Set.uIcc_of_le hT]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [pascalSymmetricRectangleRightEdge, hσ]
    · simp [pascalSymmetricRectangleRightEdge]
    · simpa [pascalSymmetricRectangleRightEdge] using ht
  · intro t ht
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [pascalSymmetricRectangleLeftEdge]
    · simp [pascalSymmetricRectangleLeftEdge, hσ]
    · simpa [pascalSymmetricRectangleLeftEdge] using ht
  · intro u hu
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change 1 - W.rectangle.σ ≤
        (pascalSymmetricRectangleTopEdge u W.rectangle.T).re
      simpa [pascalSymmetricRectangleTopEdge] using hu.1
    · change (pascalSymmetricRectangleTopEdge u W.rectangle.T).re ≤
        W.rectangle.σ
      simpa [pascalSymmetricRectangleTopEdge] using hu.2
    · change -W.rectangle.T ≤
        (pascalSymmetricRectangleTopEdge u W.rectangle.T).im
      simp [pascalSymmetricRectangleTopEdge, hT]
    · change (pascalSymmetricRectangleTopEdge u W.rectangle.T).im ≤
        W.rectangle.T
      simp [pascalSymmetricRectangleTopEdge]
  · intro u hu
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change 1 - W.rectangle.σ ≤
        (pascalSymmetricRectangleBottomEdge u W.rectangle.T).re
      simpa [pascalSymmetricRectangleBottomEdge] using hu.1
    · change (pascalSymmetricRectangleBottomEdge u W.rectangle.T).re ≤
        W.rectangle.σ
      simpa [pascalSymmetricRectangleBottomEdge] using hu.2
    · change -W.rectangle.T ≤
        (pascalSymmetricRectangleBottomEdge u W.rectangle.T).im
      simp [pascalSymmetricRectangleBottomEdge]
    · change (pascalSymmetricRectangleBottomEdge u W.rectangle.T).im ≤
        W.rectangle.T
      simp [pascalSymmetricRectangleBottomEdge, hT]

/-- The raw disk regularizer is interval-integrable on all four oriented
rectangle edges.  This theorem supplies the integrability needed before the
raw/principal-part decomposition is integrated. -/
theorem pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedRawRegularizer
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiDiskWeightedRawRegularizer h W.R
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T := by
  obtain ⟨hR, hL, hT, hB⟩ :=
    pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_rectangleBoundary
      (h := h) W
  obtain ⟨eR, eL, eT, eB⟩ := pascalCenteredXiRectangle_edge_mem_closed W
  have hpatchedR : IntervalIntegrable
      (fun t => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) * Complex.I)
      volume (-W.rectangle.T) W.rectangle.T := by
    apply (ContinuousOn.intervalIntegrable)
    intro t ht
    have hedge : ContinuousAt
        (pascalSymmetricRectangleRightEdge W.rectangle.σ) t := by
      change ContinuousAt
        (fun x : ℝ => (W.rectangle.σ : ℂ) + (x : ℂ) * Complex.I) t
      fun_prop
    exact ((continuousAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered
      hh W (eR t ht)).comp hedge).continuousWithinAt.mul
        continuousAt_const.continuousWithinAt
  have hpatchedL : IntervalIntegrable
      (fun t => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleLeftEdge W.rectangle.σ t)) * Complex.I)
      volume W.rectangle.T (-W.rectangle.T) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.uIcc (-W.rectangle.T) W.rectangle.T := by
      simpa [Set.uIcc_comm] using ht
    have hedge : ContinuousAt
        (pascalSymmetricRectangleLeftEdge W.rectangle.σ) t := by
      change ContinuousAt
        (fun x : ℝ => ((1 - W.rectangle.σ : ℝ) : ℂ) +
          (x : ℂ) * Complex.I) t
      fun_prop
    exact ((continuousAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered
      hh W (eL t ht')).comp hedge).continuousWithinAt.mul
        continuousAt_const.continuousWithinAt
  have hpatchedT : IntervalIntegrable
      (fun u => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)))
      volume W.rectangle.σ (1 - W.rectangle.σ) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Set.uIcc (1 - W.rectangle.σ) W.rectangle.σ := by
      simpa [Set.uIcc_comm] using hu
    have hedge : ContinuousAt
        (fun x : ℝ => pascalSymmetricRectangleTopEdge x W.rectangle.T) u := by
      change ContinuousAt
        (fun x : ℝ => (x : ℂ) + (W.rectangle.T : ℂ) * Complex.I) u
      fun_prop
    simpa only [Function.comp_def] using
      (ContinuousAt.comp
        (f := fun x : ℝ => pascalSymmetricRectangleTopEdge x W.rectangle.T)
        (x := u)
        (g := fun s : ℂ => pascalCenteredXiDiskWeightedRegularizer h W.R
          (pascalOrdinaryToCentered s))
        (continuousAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered
          hh W (eT u hu')) hedge).continuousWithinAt
  have hpatchedB : IntervalIntegrable
      (fun u => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleBottomEdge u W.rectangle.T)))
      volume (1 - W.rectangle.σ) W.rectangle.σ := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hedge : ContinuousAt
        (fun x : ℝ => pascalSymmetricRectangleBottomEdge x W.rectangle.T) u := by
      change ContinuousAt
        (fun x : ℝ => (x : ℂ) - (W.rectangle.T : ℂ) * Complex.I) u
      fun_prop
    simpa only [Function.comp_def] using
      (ContinuousAt.comp
        (f := fun x : ℝ => pascalSymmetricRectangleBottomEdge x W.rectangle.T)
        (x := u)
        (g := fun s : ℂ => pascalCenteredXiDiskWeightedRegularizer h W.R
          (pascalOrdinaryToCentered s))
        (continuousAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered
          hh W (eB u hu)) hedge).continuousWithinAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hpatchedR.congr
    intro t ht
    simpa using congrArg (fun z : ℂ => z * Complex.I) (hR t)
  · apply hpatchedT.congr
    intro u hu
    simpa using hT u
  · apply hpatchedL.congr
    intro t ht
    simpa using congrArg (fun z : ℂ => z * Complex.I) (hL t)
  · apply hpatchedB.congr
    intro u hu
    simpa using hB u

/-! ## Gate E: coordinate-safe raw decomposition -/

/-- The fixed-Xi weighted negative-log-derivative decomposition, pulled back
to ordinary rectangle coordinates.  This is a pointwise definitional
identity; it introduces no analytic continuation or contour argument. -/
theorem pascalCenteredXiWeightedNegLogDeriv_comp_toCentered_eq_raw_add_principalPartSum
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) (s : ℂ) :
    pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered s) =
      pascalCenteredXiDiskWeightedRawRegularizer h W.R
          (pascalOrdinaryToCentered s) +
        pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
          (pascalOrdinaryToCentered s) := by
  unfold pascalCenteredXiWeightedNegLogDeriv
    pascalCenteredXiDiskWeightedRawRegularizer
  ring

/-! ## Gate F: fixed-Xi rectangle residue formula -/

/-- The finite fixed-Xi rectangle contribution equals the finite weighted
zero moment.  The proof is the actual sum of the raw zero integral and the
finite principal-part rectangle charge; it is not a deformation theorem. -/
theorem pascalCenteredXiWeightedRectangleContribution_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiRectangleContribution h W.toContourTransportWindow =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R := by
  have hraw := pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedRawRegularizer
    hh W
  have hprincipal :=
    pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedPrincipalPartSum h W
  have hdecomp :
      (fun s : ℂ => pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered s)) =
      (fun s : ℂ => pascalCenteredXiDiskWeightedRawRegularizer h W.R
        (pascalOrdinaryToCentered s) +
        pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
          (pascalOrdinaryToCentered s)) := by
    funext s
    exact pascalCenteredXiWeightedNegLogDeriv_comp_toCentered_eq_raw_add_principalPartSum
      h W s
  change pascalSymmetricRectangleBoundaryIntegral
      (fun s : ℂ => pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T = _
  rw [hdecomp,
    pascalSymmetricRectangleBoundaryIntegral_add
      (fun s : ℂ => pascalCenteredXiDiskWeightedRawRegularizer h W.R
        (pascalOrdinaryToCentered s))
      (fun s : ℂ => pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
        (pascalOrdinaryToCentered s)) hraw hprincipal,
    pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero hh W,
    pascalCenteredXiRectangleIntegral_diskWeightedPrincipalPartSum_eq h W]
  simp

/-! ## Gate G: common finite residue endpoint -/

/-- The fixed rectangle and centered outer circle agree through their common
finite weighted zero-moment endpoint.  This is an equality of two already
evaluated finite formulas, not a homotopy or contour-deformation theorem. -/
theorem pascalCenteredXiWeightedRectangleContribution_eq_outerContourMass
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiRectangleContribution h W.toContourTransportWindow =
      pascalCenteredXiWeightedOuterContourMass h W.R := by
  rw [pascalCenteredXiWeightedRectangleContribution_eq hh W,
    pascalCenteredXiWeightedOuterContourMass_eq hh W.circle_safe]

/-! ## Gate H: finite explicit-formula skeleton -/

/-- The finite-height fixed-Xi explicit-formula skeleton.  The horizontal term
is retained at the fixed finite height `W.rectangle.T`; no decay or limit is
used. -/
theorem pascalCenteredXiFiniteExplicitFormulaSkeleton
    {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R =
      2 * (∫ t in (-W.rectangle.T)..W.rectangle.T,
        (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I) +
        2 * pascalCenteredXiTopHorizontalContribution h
          W.toContourTransportWindow := by
  calc
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R =
      pascalCenteredXiRectangleContribution h W.toContourTransportWindow := by
        symm
        exact pascalCenteredXiWeightedRectangleContribution_eq hdiff W
    _ = 2 * (∫ t in (-W.rectangle.T)..W.rectangle.T,
        (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I) +
        2 * pascalCenteredXiTopHorizontalContribution h
          W.toContourTransportWindow :=
      pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
        heven W.toContourTransportWindow

end DkMath.RH.CFBRCProjection
