/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Fixed-Xi circle-to-rectangle residue transport

This module transports the cancellation-complete centered-Xi observable from
the existing finite outer circle to a finite symmetric rectangle.  The
rectangle is governed by an explicit stronger window: the original
same-zero-set contract, a safe circle radius, and nonvanishing on all four
rectangle edges.

The rectangle Cauchy-Goursat part is proved through Mathlib's pinned
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
API.  Any one-pole rectangle charge is kept as a named provider boundary
below if the pinned API does not make that charge available without building
a new residue framework.  No homotopy, limiting operation, prime cutoff
exchange, defect vanishing, or RH statement is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open Set
open scoped Interval Topology

/-! ## Gate A: rectangle sets and the Mathlib boundary adapter -/

/-- The ordinary closed rectangle used by Mathlib's `uIcc ×ℂ uIcc` API. -/
def pascalSymmetricRectangleClosed (σ T : ℝ) : Set ℂ :=
  Set.uIcc (1 - σ) σ ×ℂ Set.uIcc (-T) T

/-- The ordinary open rectangle written in the product form used by Mathlib. -/
def pascalSymmetricRectangleOpen (σ T : ℝ) : Set ℂ :=
  Set.Ioo (1 - σ) σ ×ℂ Set.Ioo (-T) T

/-- The four-edge nonvanishing predicate for a centered-Xi rectangle. -/
def IsPascalCenteredXiRectangleBoundarySafe
    (W : PascalCenteredXiContourTransportWindow) : Prop :=
  (∀ t : ℝ,
    pascalCenteredRiemannXiKernel
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) ≠ 0) ∧
  (∀ t : ℝ,
    pascalCenteredRiemannXiKernel
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleLeftEdge W.rectangle.σ t)) ≠ 0) ∧
  (∀ u : ℝ,
    pascalCenteredRiemannXiKernel
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) ≠ 0) ∧
  (∀ u : ℝ,
    pascalCenteredRiemannXiKernel
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleBottomEdge u W.rectangle.T)) ≠ 0)

/-- A same-zero-set window equipped with the two boundary-safety contracts
needed for residue transport.  The circle and rectangle safety hypotheses are
inputs; they are not inferred from the finite geometry. -/
structure PascalCenteredXiResidueTransportWindow
    extends PascalCenteredXiContourTransportWindow where
  circle_safe : IsPascalCenteredXiBoundarySafeRadius R
  rectangle_boundary_safe :
    IsPascalCenteredXiRectangleBoundarySafe toPascalCenteredXiContourTransportWindow

/-- Forget the stronger safety fields and recover the XDP-009 contour window. -/
def PascalCenteredXiResidueTransportWindow.toContourTransportWindow
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiContourTransportWindow :=
  W.toPascalCenteredXiContourTransportWindow

/-- The four-edge boundary used in this development agrees with the pinned
Mathlib rectangle boundary expression, after choosing the lower-left and
upper-right corners in ordinary coordinates. -/
theorem pascalSymmetricRectangleBoundaryIntegral_eq_mathlibBoundary
    (F : ℂ → ℂ) (σ T : ℝ) :
    pascalSymmetricRectangleBoundaryIntegral F σ T =
      (∫ x in (1 - σ)..σ,
        F (pascalSymmetricRectangleBottomEdge x T)) -
      (∫ x in (1 - σ)..σ,
        F (pascalSymmetricRectangleTopEdge x T)) +
      Complex.I • (∫ y in (-T)..T,
        F (pascalSymmetricRectangleRightEdge σ y)) -
      Complex.I • (∫ y in (-T)..T,
        F (pascalSymmetricRectangleLeftEdge σ y)) := by
  unfold pascalSymmetricRectangleBoundaryIntegral
  rw [intervalIntegral.integral_symm (1 - σ) σ]
  rw [intervalIntegral.integral_symm (-T) T]
  simp only [intervalIntegral.integral_mul_const]
  ring

/-- The explicit closed rectangle is the `uIcc ×ℂ uIcc` rectangle seen by
Mathlib when its opposite corners are chosen from the XDP geometry. -/
theorem pascalSymmetricRectangleClosed_eq_mathlibClosed
    {σ T : ℝ} (_hσ : 1 < σ) (hT : 0 < T) :
    pascalSymmetricRectangleClosed σ T =
      Set.uIcc
          (pascalSymmetricRectangleLeftEdge σ (-T)).re
          (pascalSymmetricRectangleRightEdge σ T).re ×ℂ
        Set.uIcc
          (pascalSymmetricRectangleLeftEdge σ (-T)).im
          (pascalSymmetricRectangleRightEdge σ T).im := by
  ext s
  simp [pascalSymmetricRectangleClosed, pascalSymmetricRectangleLeftEdge,
    pascalSymmetricRectangleRightEdge, Set.uIcc_of_le, hT.le]

/-- The explicit open rectangle is the open rectangle in the pinned
Mathlib Cauchy-Goursat theorem. -/
theorem pascalSymmetricRectangleOpen_eq_mathlibOpen
    {σ T : ℝ} (_hσ : 1 < σ) (_hT : 0 < T) :
    pascalSymmetricRectangleOpen σ T =
      Set.Ioo
          (pascalSymmetricRectangleLeftEdge σ (-T)).re
          (pascalSymmetricRectangleRightEdge σ T).re ×ℂ
        Set.Ioo
          (pascalSymmetricRectangleLeftEdge σ (-T)).im
          (pascalSymmetricRectangleRightEdge σ T).im := by
  ext s
  simp [pascalSymmetricRectangleOpen, pascalSymmetricRectangleLeftEdge,
    pascalSymmetricRectangleRightEdge]

/-! ## Gate B: zero localization supplied by the stronger window -/

/-- A closed rectangle point which is not in the open rectangle lies on one
of the four oriented edges. -/
theorem mem_pascalSymmetricRectangleClosed_not_mem_open_imp_mem_edge
    {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T) {s : ℂ}
    (hsClosed : s ∈ pascalSymmetricRectangleClosed σ T)
    (hsOpen : s ∉ pascalSymmetricRectangleOpen σ T) :
    s.re = 1 - σ ∨ s.re = σ ∨ s.im = -T ∨ s.im = T := by
  simp only [pascalSymmetricRectangleClosed, pascalSymmetricRectangleOpen]
    at hsClosed hsOpen ⊢
  have hσ' : 1 - σ ≤ σ := by linarith
  have hT' : -T ≤ T := by linarith
  rw [Set.uIcc_of_le hσ', Set.uIcc_of_le hT'] at hsClosed
  rcases hsClosed with ⟨⟨hsr₁, hsr₂⟩, ⟨hsi₁, hsi₂⟩⟩
  by_cases h₁ : 1 - σ < s.re
  · by_cases h₂ : s.re < σ
    · by_cases h₃ : -T < s.im
      · by_cases h₄ : s.im < T
        · exact (hsOpen ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩).elim
        · exact Or.inr (Or.inr (Or.inr (le_antisymm hsi₂ (le_of_not_gt h₄))))
      · exact Or.inr (Or.inr (Or.inl (le_antisymm (le_of_not_gt h₃) hsi₁)))
    · exact Or.inr (Or.inl (le_antisymm hsr₂ (le_of_not_gt h₂)))
  · exact Or.inl (le_antisymm (le_of_not_gt h₁) hsr₁)

/-- Every centered-Xi zero in the closed rectangle belongs to the disk
principal-part finset.  Interior membership comes from `zero_mem_iff`; a
boundary point is excluded by the four-edge safety contract. -/
theorem mem_pascalCenteredXiZeroDiskFinset_of_mem_closedRectangle
    (W : PascalCenteredXiResidueTransportWindow) {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeros)
    (hzClosed : pascalCenteredToOrdinary z ∈
      pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) :
    z ∈ pascalCenteredXiZeroDiskFinset W.R := by
  have hsOpenOr : pascalCenteredToOrdinary z ∈
      pascalSymmetricRectangleOpen W.rectangle.σ W.rectangle.T := by
    by_contra hsOpen
    have hedge := mem_pascalSymmetricRectangleClosed_not_mem_open_imp_mem_edge
      W.rectangle.hσ W.rectangle.hT hzClosed hsOpen
    rcases hedge with hleft | hrest
    · have hsEq : pascalCenteredToOrdinary z =
          pascalSymmetricRectangleLeftEdge W.rectangle.σ z.im := by
        apply Complex.ext
        · simpa [pascalCenteredToOrdinary, pascalSymmetricRectangleLeftEdge,
            criticalLineCenter] using hleft
        · simp [pascalCenteredToOrdinary, pascalSymmetricRectangleLeftEdge]
      exact (W.rectangle_boundary_safe.2.1 z.im) (by
        rw [← hsEq]
        simpa [pascalOrdinaryToCentered, pascalCenteredToOrdinary] using
          (mem_pascalCenteredXiZeros.mp hz))
    · rcases hrest with hright | hrest
      · have hsEq : pascalCenteredToOrdinary z =
            pascalSymmetricRectangleRightEdge W.rectangle.σ z.im := by
          apply Complex.ext
          · simpa [pascalCenteredToOrdinary, pascalSymmetricRectangleRightEdge,
              criticalLineCenter] using hright
          · simp [pascalCenteredToOrdinary, pascalSymmetricRectangleRightEdge]
        exact (W.rectangle_boundary_safe.1 z.im) (by
          rw [← hsEq]
          simpa [pascalOrdinaryToCentered, pascalCenteredToOrdinary] using
            (mem_pascalCenteredXiZeros.mp hz))
      · rcases hrest with hbottom | htop
        · have hsEq : pascalCenteredToOrdinary z =
              pascalSymmetricRectangleBottomEdge
                (pascalCenteredToOrdinary z).re W.rectangle.T := by
            apply Complex.ext
            · simp [pascalCenteredToOrdinary, pascalSymmetricRectangleBottomEdge]
            · simpa [pascalCenteredToOrdinary, pascalSymmetricRectangleBottomEdge] using
                hbottom
          exact (W.rectangle_boundary_safe.2.2.2
            (pascalCenteredToOrdinary z).re) (by
            rw [← hsEq]
            simpa [pascalOrdinaryToCentered, pascalCenteredToOrdinary] using
              (mem_pascalCenteredXiZeros.mp hz))
        · have hsEq : pascalCenteredToOrdinary z =
              pascalSymmetricRectangleTopEdge
                (pascalCenteredToOrdinary z).re W.rectangle.T := by
            apply Complex.ext
            · simp [pascalCenteredToOrdinary, pascalSymmetricRectangleTopEdge]
            · simpa [pascalCenteredToOrdinary, pascalSymmetricRectangleTopEdge] using
                htop
          exact (W.rectangle_boundary_safe.2.2.1
            (pascalCenteredToOrdinary z).re) (by
            rw [← hsEq]
            simpa [pascalOrdinaryToCentered, pascalCenteredToOrdinary] using
              (mem_pascalCenteredXiZeros.mp hz))
  apply (mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe W.circle_safe).2
  refine ⟨(W.zero_mem_iff z hz).2 ?_, hz⟩
  rcases hsOpenOr with ⟨hsr, hsi⟩
  exact ⟨hsr.1, hsr.2, hsi.1, hsi.2⟩

/-- A closed-rectangle point outside the finite disk zero set is a
nonvanishing point of the centered Xi kernel. -/
theorem pascalCenteredXiKernel_ne_zero_of_mem_closedRectangle_not_mem_disk
    (W : PascalCenteredXiResidueTransportWindow) {z : ℂ}
    (hzClosed : pascalCenteredToOrdinary z ∈
      pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T)
    (hzS : z ∉ pascalCenteredXiZeroDiskFinset W.R) :
    pascalCenteredRiemannXiKernel z ≠ 0 := by
  intro hzero
  apply hzS
  exact mem_pascalCenteredXiZeroDiskFinset_of_mem_closedRectangle W
    (mem_pascalCenteredXiZeros.mpr hzero) hzClosed

/-! ## Gate C/D: regularizer regularity on the rectangle -/

/-- The patched regularizer, composed with the ordinary-to-centered
translation, is continuous at every closed-rectangle point. -/
theorem continuousAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) {s : ℂ}
    (hsClosed : s ∈ pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) :
    ContinuousAt
      (fun x => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered x)) s := by
  have hto : ContinuousAt pascalOrdinaryToCentered s := by
    change ContinuousAt (fun x : ℂ => x - criticalLineCenter) s
    fun_prop
  by_cases hzS : pascalOrdinaryToCentered s ∈
      pascalCenteredXiZeroDiskFinset W.R
  · exact (pascalCenteredXiDiskWeightedRegularizer_continuousAt_of_mem hh hzS).comp
      hto
  · have hXi := pascalCenteredXiKernel_ne_zero_of_mem_closedRectangle_not_mem_disk
      W (z := pascalOrdinaryToCentered s)
        (by simpa only [pascalCenteredToOrdinary_pascalOrdinaryToCentered] using hsClosed)
        hzS
    have hreg : ContinuousAt (pascalCenteredXiDiskWeightedRegularizer h W.R)
        (pascalOrdinaryToCentered s) := by
      rw [continuousAt_congr
        (pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_raw_of_not_mem hzS)]
      exact (differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer_of_kernel_ne_zero
        hh hXi hzS).continuousAt
    exact hreg.comp hto

/-- The patched regularizer is complex differentiable in the open rectangle
away from the finite principal-part zero set. -/
theorem differentiableAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered_of_not_mem
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) {s : ℂ}
    (hsOpen : s ∈ pascalSymmetricRectangleOpen W.rectangle.σ W.rectangle.T)
    (hsS : pascalOrdinaryToCentered s ∉ pascalCenteredXiZeroDiskFinset W.R) :
    DifferentiableAt ℂ
      (fun x => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered x)) s := by
  have hsInterior : s ∈ pascalSymmetricRectangleInterior
      W.rectangle.σ W.rectangle.T := by
    rcases hsOpen with ⟨⟨hsr₁, hsr₂⟩, ⟨hsi₁, hsi₂⟩⟩
    exact ⟨hsr₁, hsr₂, hsi₁, hsi₂⟩
  have hXi : pascalCenteredRiemannXiKernel
      (pascalOrdinaryToCentered s) ≠ 0 := by
    intro hzero
    apply hsS
    exact (mem_pascalCenteredXiZeroDiskFinset_iff).2
      ⟨Metric.mem_closedBall.mpr (le_of_lt
          ((W.zero_mem_iff _ (mem_pascalCenteredXiZeros.mpr hzero)).2
            (by simpa [pascalCenteredToOrdinary, pascalOrdinaryToCentered] using hsInterior))),
        mem_pascalCenteredXiZeros.mpr hzero⟩
  have hto : DifferentiableAt ℂ pascalOrdinaryToCentered s := by
    change DifferentiableAt ℂ (fun x : ℂ => x - criticalLineCenter) s
    fun_prop
  have hreg : DifferentiableAt ℂ (pascalCenteredXiDiskWeightedRegularizer h W.R)
      (pascalOrdinaryToCentered s) := by
    apply (pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_raw_of_not_mem
      (h := h) (R := W.R) hsS).differentiableAt_iff.mpr
    exact differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer_of_kernel_ne_zero
      hh hXi hsS
  exact hreg.comp s hto

/-! ## Gate E provider boundary -/

/-- Conditional one-pole rectangle charge provider.

This is deliberately a provider rather than an axiom or an existence
theorem.  The pinned Cauchy-Goursat API supplies the regularizer-zero part,
but a one-pole rectangle charge is not silently identified with a residue
without a separate theorem. -/
structure PascalCenteredXiRectanglePrincipalPartChargeProvider
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) where
  principalPart_boundary_eq : ∀ {a : ℂ},
    a ∈ pascalCenteredXiZeroDiskFinset W.R →
    pascalSymmetricRectangleBoundaryIntegral
      (fun s => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity a : ℂ) * h a

/-! ## Gate D: patched regularizer Cauchy-Goursat -/

/-- The patched disk regularizer has zero integral on the finite rectangle.

The exceptional set supplied to Mathlib is the ordinary-coordinate image of
the centered disk zero finset.  The stronger window supplies continuity on the
closed rectangle and differentiability away from that finite set. -/
theorem pascalCenteredXiRectangleIntegral_diskWeightedRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalSymmetricRectangleBoundaryIntegral
      (fun s => pascalCenteredXiDiskWeightedRegularizer h W.R
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T = 0 := by
  let F : ℂ → ℂ := fun s => pascalCenteredXiDiskWeightedRegularizer h W.R
    (pascalOrdinaryToCentered s)
  let z₀ : ℂ := pascalSymmetricRectangleLeftEdge W.rectangle.σ
    (-W.rectangle.T)
  let w₀ : ℂ := pascalSymmetricRectangleRightEdge W.rectangle.σ
    W.rectangle.T
  have hclosed : ContinuousOn F
      (pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T) := by
    intro s hs
    exact continuousAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered
      hh W hs |>.continuousWithinAt
  have hmathClosed : ContinuousOn F ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) := by
    rw [show ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) =
        pascalSymmetricRectangleClosed W.rectangle.σ W.rectangle.T by
      simpa [z₀, w₀] using
        (pascalSymmetricRectangleClosed_eq_mathlibClosed
          W.rectangle.hσ W.rectangle.hT).symm]
    exact hclosed
  let exceptional : Set ℂ := pascalCenteredToOrdinary ''
    (pascalCenteredXiZeroDiskFinset W.R : Set ℂ)
  have hexceptional : exceptional.Countable := by
    exact (pascalCenteredXiZeroDiskFinset W.R).countable_toSet.image _
  have hmathDiff : ∀ s ∈ Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ
      Ioo (min z₀.im w₀.im) (max z₀.im w₀.im) \ exceptional,
      DifferentiableAt ℂ F s := by
    intro s hs
    have hsOpen : s ∈ pascalSymmetricRectangleOpen
        W.rectangle.σ W.rectangle.T := by
      have hopen_eq : pascalSymmetricRectangleOpen
          W.rectangle.σ W.rectangle.T =
          Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ
            Ioo (min z₀.im w₀.im) (max z₀.im w₀.im) := by
        have hσ' : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
          linarith [W.rectangle.hσ]
        have hT' : -W.rectangle.T ≤ W.rectangle.T := by
          linarith [W.rectangle.hT]
        simpa [z₀, w₀, pascalSymmetricRectangleLeftEdge,
          pascalSymmetricRectangleRightEdge, min_eq_left hσ',
          max_eq_right hσ', min_eq_left hT', max_eq_right hT'] using
          (pascalSymmetricRectangleOpen_eq_mathlibOpen
            W.rectangle.hσ W.rectangle.hT)
      rw [hopen_eq]
      exact hs.1
    have hsS : pascalOrdinaryToCentered s ∉
        pascalCenteredXiZeroDiskFinset W.R := by
      intro hsS
      apply hs.2
      exact ⟨pascalOrdinaryToCentered s, hsS, by
        exact pascalCenteredToOrdinary_pascalOrdinaryToCentered s⟩
    exact differentiableAt_pascalCenteredXiDiskWeightedRegularizer_comp_toCentered_of_not_mem
      hh W hsOpen hsS
  have hmath :=
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      F z₀ w₀ exceptional hexceptional hmathClosed hmathDiff
  change pascalSymmetricRectangleBoundaryIntegral F
      W.rectangle.σ W.rectangle.T = 0
  rw [pascalSymmetricRectangleBoundaryIntegral_eq_mathlibBoundary]
  simpa [z₀, w₀, pascalSymmetricRectangleLeftEdge,
    pascalSymmetricRectangleRightEdge, pascalSymmetricRectangleTopEdge,
    pascalSymmetricRectangleBottomEdge, smul_eq_mul, sub_eq_add_neg] using hmath

/-! ## Gate D boundary congruence -/

/-- Boundary safety identifies the patched and raw disk regularizers on each
oriented rectangle edge.  This is a pointwise boundary statement; it does
not identify the totalized value of `logDeriv` at a zero with a removable
value. -/
theorem pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_rectangleBoundary
    {h : ℂ → ℂ} (W : PascalCenteredXiResidueTransportWindow) :
    (∀ t : ℝ,
      pascalCenteredXiDiskWeightedRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) =
        pascalCenteredXiDiskWeightedRawRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) ∧
    (∀ t : ℝ,
      pascalCenteredXiDiskWeightedRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleLeftEdge W.rectangle.σ t)) =
        pascalCenteredXiDiskWeightedRawRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleLeftEdge W.rectangle.σ t))) ∧
    (∀ u : ℝ,
      pascalCenteredXiDiskWeightedRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
        pascalCenteredXiDiskWeightedRawRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))) ∧
    (∀ u : ℝ,
      pascalCenteredXiDiskWeightedRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleBottomEdge u W.rectangle.T)) =
        pascalCenteredXiDiskWeightedRawRegularizer h W.R
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleBottomEdge u W.rectangle.T))) := by
  have hedge (z : ℂ) (hz : pascalCenteredRiemannXiKernel z ≠ 0) :
      pascalCenteredXiDiskWeightedRegularizer h W.R z =
        pascalCenteredXiDiskWeightedRawRegularizer h W.R z := by
    by_cases hzS : z ∈ pascalCenteredXiZeroDiskFinset W.R
    · exact (hz (mem_pascalCenteredXiZeros.mp
        (mem_pascalCenteredXiZeroDiskFinset_iff.mp hzS).2)).elim
    · simp [pascalCenteredXiDiskWeightedRegularizer, hzS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact hedge _ (W.rectangle_boundary_safe.1 t)
  · intro t
    exact hedge _ (W.rectangle_boundary_safe.2.1 t)
  · intro u
    exact hedge _ (W.rectangle_boundary_safe.2.2.1 u)
  · intro u
    exact hedge _ (W.rectangle_boundary_safe.2.2.2 u)

/-- The raw disk regularizer has zero integral on the finite rectangle. -/
theorem pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalSymmetricRectangleBoundaryIntegral
      (fun s => pascalCenteredXiDiskWeightedRawRegularizer h W.R
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T = 0 := by
  obtain ⟨hright, hleft, htop, hbottom⟩ :=
    pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_rectangleBoundary
      (h := h) W
  have hboundary :
      pascalSymmetricRectangleBoundaryIntegral
          (fun s => pascalCenteredXiDiskWeightedRegularizer h W.R
            (pascalOrdinaryToCentered s))
          W.rectangle.σ W.rectangle.T =
        pascalSymmetricRectangleBoundaryIntegral
          (fun s => pascalCenteredXiDiskWeightedRawRegularizer h W.R
            (pascalOrdinaryToCentered s))
          W.rectangle.σ W.rectangle.T := by
    unfold pascalSymmetricRectangleBoundaryIntegral
    rw [intervalIntegral.integral_congr (fun t _ =>
      congrArg (fun z : ℂ => z * Complex.I) (hright t))]
    rw [intervalIntegral.integral_congr (fun u _ => htop u)]
    rw [intervalIntegral.integral_congr (fun t _ =>
      congrArg (fun z : ℂ => z * Complex.I) (hleft t))]
    rw [intervalIntegral.integral_congr (fun u _ => hbottom u)]
  rw [← hboundary]
  exact pascalCenteredXiRectangleIntegral_diskWeightedRegularizer_eq_zero hh W

end DkMath.RH.CFBRCProjection
