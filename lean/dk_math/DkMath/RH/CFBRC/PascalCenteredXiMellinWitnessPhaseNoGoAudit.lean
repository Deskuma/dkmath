/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessArithmeticControlAudit
import Mathlib.Tactic

/-!
# GWSS-003B: complex-linear phase no-go audit

The finite arithmetic right-hand side is directly complex-linear in the
admissible weight.  Since differentiability and centered evenness are closed
under multiplication by `Complex.I`, a universal theorem forcing that RHS
onto one fixed real line would force the whole RHS to vanish.  This module
proves that finite algebraic obstruction without using the zero-side explicit
formula as an arithmetic provider.

The module also records a small conjugation-real predicate as an audit aid.
It does not assert that the canonical Mellin family or the target-dependent
inverse-matrix witness lies in that real form; the corresponding API remains a
separate compatibility question.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped Interval Topology

/-! ## GWSS-003B-1: complex scalar linearity -/

/-- Multiplication by a complex scalar preserves centered evenness. -/
theorem pascalCenteredEvenWeight_const_mul
    {h : ℂ → ℂ} (heven : PascalCenteredEvenWeight h) (a : ℂ) :
    PascalCenteredEvenWeight (fun z => a * h z) := by
  intro z
  change a * h (-z) = a * h z
  rw [heven z]

/-- Multiplication by a complex scalar preserves differentiability. -/
theorem pascalCenteredXiDifferentiable_const_mul
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (a : ℂ) :
    Differentiable ℂ (fun z => a * h z) := by
  exact (differentiable_const (c := a)).mul hh

/-- The centered Xi zero moment is complex-linear in the weight.

This is a comparison lemma only; the arithmetic RHS linearity below is proved
directly from its four finite interval-integral terms.
-/
theorem pascalCenteredXiZeroDiskWeightedMoment_const_mul
    (a : ℂ) (h : ℂ → ℂ) (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment (fun z => a * h z) R =
      a * pascalCenteredXiZeroDiskWeightedMoment h R := by
  unfold pascalCenteredXiZeroDiskWeightedMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- The finite arithmetic RHS is complex-linear in the weight.

The proof uses only scalar multiplication of each finite interval integral and
keeps the top-horizontal term explicit.  It therefore does not obtain
linearity by rewriting through the zero-side moment identity.
-/
theorem pascalCenteredXiFiniteArithmeticRHS_const_mul
    (a : ℂ) (h : ℂ → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiFiniteArithmeticRHS (fun z => a * h z) W =
      a * pascalCenteredXiFiniteArithmeticRHS h W := by
  have hOrd :
      pascalXiOrdinaryZetaRightEdgeIntegral (fun z => a * h z)
          W.rectangle.σ W.rectangle.T =
        a * pascalXiOrdinaryZetaRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T := by
    unfold pascalXiOrdinaryZetaRightEdgeIntegral
      pascalXiOrdinaryZetaRightEdgeIntegrand
    rw [show
      (fun t : ℝ =>
        (fun z => a * h z) (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiOrdinaryZetaNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) *
          Complex.I) =
        (fun t : ℝ => a *
          ((h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalXiOrdinaryZetaNegLogDeriv
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            Complex.I)) by
          funext t
          ring]
    exact intervalIntegral.integral_const_mul a _
  have hArch :
      pascalXiArchimedeanRightEdgeIntegral (fun z => a * h z)
          W.rectangle.σ W.rectangle.T =
        a * pascalXiArchimedeanRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T := by
    unfold pascalXiArchimedeanRightEdgeIntegral
      pascalXiArchimedeanRightEdgeIntegrand
    rw [show
      (fun t : ℝ =>
        (fun z => a * h z) (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiArchimedeanLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) *
          Complex.I) =
        (fun t : ℝ => a *
          ((h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalXiArchimedeanLogDeriv
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            Complex.I)) by
          funext t
          ring]
    exact intervalIntegral.integral_const_mul a _
  have hElem :
      pascalXiElementaryRightEdgeIntegral (fun z => a * h z)
          W.rectangle.σ W.rectangle.T =
        a * pascalXiElementaryRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T := by
    unfold pascalXiElementaryRightEdgeIntegral
      pascalXiElementaryRightEdgeIntegrand
    rw [show
      (fun t : ℝ =>
        (fun z => a * h z) (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiElementaryLogDerivCorrection
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) *
          Complex.I) =
        (fun t : ℝ => a *
          ((h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalXiElementaryLogDerivCorrection
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            Complex.I)) by
          funext t
          ring]
    exact intervalIntegral.integral_const_mul a _
  have hTop :
      pascalCenteredXiTopHorizontalContribution (fun z => a * h z)
          W.toContourTransportWindow =
        a * pascalCenteredXiTopHorizontalContribution h
          W.toContourTransportWindow := by
    unfold pascalCenteredXiTopHorizontalContribution
      pascalCenteredXiWeightedNegLogDeriv
    rw [show
      (fun u : ℝ =>
        (fun z => a * h z) (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u W.toContourTransportWindow.rectangle.T)) *
          pascalCenteredXiNegLogDeriv
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.toContourTransportWindow.rectangle.T))) =
        (fun u : ℝ => a *
          (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.toContourTransportWindow.rectangle.T)) *
              pascalCenteredXiNegLogDeriv
              (pascalOrdinaryToCentered
                (pascalSymmetricRectangleTopEdge u W.toContourTransportWindow.rectangle.T)))) by
          funext u
          ring]
    exact intervalIntegral.integral_const_mul a _
  simp only [pascalCenteredXiFiniteArithmeticRHS, hOrd, hArch, hElem, hTop]
  ring

/-! ## GWSS-003B-2: universal phase no-go -/

/-- A complex number with zero imaginary part and with zero imaginary part
after multiplication by `I` must be zero. -/
theorem complex_eq_zero_of_im_eq_zero_and_I_mul_im_eq_zero
    (w : ℂ) (h₁ : w.im = 0) (h₂ : (Complex.I * w).im = 0) :
    w = 0 := by
  apply Complex.ext
  · simpa using h₂
  · simpa using h₁

/-- The finite RHS vanishes if both `h` and `I * h` satisfy a real-axis phase
condition.  This is the local no-go statement for a complex-linear class. -/
theorem pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_im_zero_on_h_and_I_mul
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow)
    (hphase :
      (pascalCenteredXiFiniteArithmeticRHS h W).im = 0)
    (hphase_I :
      (pascalCenteredXiFiniteArithmeticRHS (fun z => Complex.I * h z) W).im = 0) :
    pascalCenteredXiFiniteArithmeticRHS h W = 0 := by
  apply complex_eq_zero_of_im_eq_zero_and_I_mul_im_eq_zero
    (pascalCenteredXiFiniteArithmeticRHS h W) hphase
  rw [← pascalCenteredXiFiniteArithmeticRHS_const_mul]
  exact hphase_I

/-- A universal real-axis phase theorem on the full differentiable/even class
would force the finite RHS to vanish on that class. -/
theorem pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_universal_im_zero
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow)
    (hphase : ∀ g : ℂ → ℂ,
      Differentiable ℂ g → PascalCenteredEvenWeight g →
        (pascalCenteredXiFiniteArithmeticRHS g W).im = 0) :
    pascalCenteredXiFiniteArithmeticRHS h W = 0 := by
  apply pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_im_zero_on_h_and_I_mul
    h W (hphase h hh heven)
  apply hphase
  · exact pascalCenteredXiDifferentiable_const_mul hh Complex.I
  · exact pascalCenteredEvenWeight_const_mul heven Complex.I

/-- The analogous universal imaginary-axis phase theorem also forces the RHS
to vanish. -/
theorem pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_universal_re_zero
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow)
    (hphase : ∀ g : ℂ → ℂ,
      Differentiable ℂ g → PascalCenteredEvenWeight g →
        (pascalCenteredXiFiniteArithmeticRHS g W).re = 0) :
    pascalCenteredXiFiniteArithmeticRHS h W = 0 := by
  have hreal := hphase h hh heven
  have hIreal := hphase (fun z => Complex.I * h z)
    (pascalCenteredXiDifferentiable_const_mul hh Complex.I)
    (pascalCenteredEvenWeight_const_mul heven Complex.I)
  have hIre :
      (Complex.I * pascalCenteredXiFiniteArithmeticRHS h W).re = 0 := by
    rw [← pascalCenteredXiFiniteArithmeticRHS_const_mul]
    exact hIreal
  have himag : (pascalCenteredXiFiniteArithmeticRHS h W).im = 0 := by
    simpa using hIre
  apply Complex.ext
  · simpa using hreal
  · exact himag

/-! ## GWSS-003B-3/4: bounded real-structure audit -/

/-- A candidate real form for centered weights, recorded without claiming that
the current Mellin witness coefficients satisfy it. -/
def PascalCenteredXiConjugationRealWeight (h : ℂ → ℂ) : Prop :=
  ∀ z, h (starRingEnd ℂ z) = starRingEnd ℂ (h z)

/-- The candidate conjugation-real class is not closed under multiplication by
`I` except at pointwise zero.  This is the structural escape from the full
complex-linear no-go, not a theorem that the current witness belongs to the
class. -/
theorem pascalCenteredXiConjugationRealWeight_I_mul_eq_zero_of_conjugationReal
    {h : ℂ → ℂ}
    (hreal : PascalCenteredXiConjugationRealWeight h)
    (hreal_I : PascalCenteredXiConjugationRealWeight (fun z => Complex.I * h z)) :
    h = 0 := by
  funext z
  change h z = 0
  have h₁ := hreal z
  have h₂ := hreal_I z
  have h₂' : Complex.I * h (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.I * h z) := h₂
  rw [h₁] at h₂'
  simp only [map_mul, Complex.conj_I] at h₂'
  have : (2 : ℂ) * (Complex.I * starRingEnd ℂ (h z)) = 0 := by
    calc
      (2 : ℂ) * (Complex.I * starRingEnd ℂ (h z)) =
          Complex.I * starRingEnd ℂ (h z) -
            (-Complex.I) * starRingEnd ℂ (h z) := by ring
      _ = 0 := by rw [← h₂']; ring
  have hstar : starRingEnd ℂ (h z) = 0 := by
    have hIstar : Complex.I * starRingEnd ℂ (h z) = 0 := by
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    exact (mul_eq_zero.mp hIstar).resolve_left (by norm_num)
  apply star_injective
  simpa using hstar

end DkMath.RH.CFBRCProjection
