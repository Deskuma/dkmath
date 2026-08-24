/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit
import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit
import Mathlib.Tactic

/-!
# GWSS-003H5: whole-source mirror conjugation transport

This module transports the H6 canonical coefficient pair through the actual
finite synthesized source surface.  The vertical source uses the reflection
`t ↦ -t`; the top source uses the affine reflection `x ↦ 1-x`.  The resulting
finite signs are

```text
vertical source = -conj (vertical source)
top source      =  conj (top source)
whole source    = -conj (whole source)
approximant     =  conj (approximant).
```

The logarithmic-box feature is treated as a finite aggregate and retains the
top `u ↦ -u` reflection.  No shifted energy, positivity, source-rank, limit,
GWSS-004, or RH statement is asserted.
 -/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open MeasureTheory
open scoped BigOperators ComplexConjugate Interval Matrix Topology

/-! ## H7-A: canonical witness-weight transport -/

/-- The canonical mirror witness weight satisfies the pulled-back Schwarz law
`hMirror z = -conj (h (conj z))`.  This needs only positive box width and the
H6 determinant hypothesis; no nonzero-`τ` logarithmic representation is used.
-/
theorem pascalCenteredXiMellinCanonicalWitnessWeight_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) (z : ℂ) :
    pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) z =
      -conj (pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        (conj z)) := by
  unfold pascalCenteredXiMellinWitnessWeight
  rw [pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror_fun
    hε τ hdet j]
  simp only [map_sum, map_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hweight := pascalCenteredXiMellinSecondDifferenceWeight_conj hε
    (τ := τ i) (conj z)
  simp only [starRingEnd_apply, star_star] at hweight ⊢
  rw [hweight]
  simp [pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow,
    pascalCenteredXiSquaredOrbitImaginaryScalar, mul_comm]

/-- The mirror witness weight evaluated at the conjugate argument has the
equivalent direct form `-conj (h z)`. -/
theorem pascalCenteredXiMellinCanonicalWitnessWeight_mirror_conj
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) (z : ℂ) :
    pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) (conj z) =
      -conj (pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j) z) := by
  simpa only [starRingEnd_apply, star_star] using
    pascalCenteredXiMellinCanonicalWitnessWeight_mirror hε τ hdet j (conj z)

/-! ## H7-B/C: finite vertical source transport -/

private theorem pascalCenteredXiMellinCanonicalWitnessWeight_rightEdge_neg_eq_neg_conj
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j))
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W (-t)) =
      -conj (pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)) := by
  rw [pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode_neg_eq_conj]
  simpa only [starRingEnd_apply, star_star] using
    pascalCenteredXiMellinCanonicalWitnessWeight_mirror_conj
      hε τ hdet j (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t)

/-- The canonical mirror vertical source is the negative conjugate of the
original finite vertical source.  The proof uses the symmetric finite height
substitution rather than identifying integrands at the same height. -/
theorem pascalCenteredXiMellinCanonicalVerticalSource_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X =
      -conj (pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j) W X) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalSource
  let g : ℝ → ℂ := fun t =>
    pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j))
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t
  let f : ℝ → ℂ := fun t =>
    pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t) *
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t
  change (∫ t in (-W.rectangle.T)..W.rectangle.T, g t) =
    -conj (∫ t in (-W.rectangle.T)..W.rectangle.T, f t)
  have hpoint (t : ℝ) :
      pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j))
          (pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W (-t)) *
        pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X (-t) =
        -conj (f t) := by
    rw [pascalCenteredXiMellinCanonicalWitnessWeight_rightEdge_neg_eq_neg_conj
      hε τ hdet j W t,
      pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_neg_eq_conj]
    dsimp [f]
    simp [map_mul]
  have hcomp :
      (∫ t in (-W.rectangle.T)..W.rectangle.T,
        g (-t)) =
        ∫ t in (-W.rectangle.T)..W.rectangle.T, g t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g)
        (a := -W.rectangle.T) (b := W.rectangle.T))
  calc
    (∫ t in (-W.rectangle.T)..W.rectangle.T, g t) =
      ∫ t in (-W.rectangle.T)..W.rectangle.T, g (-t) := by
        exact hcomp.symm
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T, -conj (f t) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        exact hpoint t
    _ = -conj (∫ t in (-W.rectangle.T)..W.rectangle.T, f t) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]

/-! ## H7-D/E: finite top source transport -/

private theorem pascalCenteredXiMellinCanonicalWitnessWeight_top_reflection
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j))
        (pascalCenteredXiPrimeSideQuadraticizationTopNode W (1 - x)) =
      -conj (pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        (pascalCenteredXiPrimeSideQuadraticizationTopNode W x)) := by
  rw [pascalCenteredXiPrimeSideQuadraticizationTopNode_one_sub_eq_neg_conj]
  rw [pascalCenteredXiMellinCanonicalWitnessWeight_mirror
    hε τ hdet j (-conj (pascalCenteredXiPrimeSideQuadraticizationTopNode W x))]
  simp only [map_neg, starRingEnd_apply, star_star]
  rw [pascalCenteredXiMellinWitnessWeight_even hε]

/-- The canonical mirror top-horizontal source is the conjugate of the
original source.  The two minus signs from the reflected weight and top
amplitude cancel before the finite horizontal integration. -/
theorem pascalCenteredXiMellinCanonicalTopSource_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j))) W.toContourTransportWindow =
      conj (pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j))
        W.toContourTransportWindow) := by
  unfold pascalCenteredXiTopHorizontalContribution
  let g : ℝ → ℂ := fun x =>
    pascalCenteredXiWeightedNegLogDeriv
      (pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)))
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge x W.rectangle.T))
  let f : ℝ → ℂ := fun x =>
    pascalCenteredXiWeightedNegLogDeriv
      (pascalCenteredXiMellinWitnessWeight ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j))
        (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge x W.rectangle.T))
  change (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), g x) =
    conj (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), f x)
  have hcomp :
      (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), g (1 - x)) =
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ), g x := by
    simpa only [sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left
        (f := g) (a := W.rectangle.σ) (b := 1 - W.rectangle.σ) (d := 1))
  have hpoint (x : ℝ) :
      g (1 - x) = conj (f x) := by
    change pascalCenteredXiWeightedNegLogDeriv
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j)))
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge (1 - x) W.rectangle.T)) =
      conj (f x)
    dsimp [f]
    change pascalCenteredXiWeightedNegLogDeriv
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j)))
        (pascalCenteredXiPrimeSideQuadraticizationTopNode W (1 - x)) =
      conj (pascalCenteredXiWeightedNegLogDeriv
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j))
        (pascalCenteredXiPrimeSideQuadraticizationTopNode W x))
    simp only [pascalCenteredXiWeightedNegLogDeriv]
    rw [pascalCenteredXiMellinCanonicalWitnessWeight_top_reflection
      hε τ hdet j W x,
      pascalCenteredXiPrimeSideQuadraticizationTopNode_one_sub_eq_neg_conj,
      pascalCenteredXiNegLogDeriv_neg, pascalCenteredXiNegLogDeriv_conj]
    simp only [map_mul, starRingEnd_apply]
    ring
  calc
    (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), g x) =
      ∫ x in W.rectangle.σ..(1 - W.rectangle.σ), g (1 - x) := by
        exact hcomp.symm
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ), conj (f x) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with x hx
        exact hpoint x
    _ = conj (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), f x) := by
      rw [intervalIntegral.intervalIntegral_conj]

/-! ## H7-F/G: whole source and finite approximant -/

/-- The whole finite source transports by negative conjugation under the
canonical critical mirror. -/
theorem pascalCenteredXiMellinCanonicalWholeSource_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X =
      -conj (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j) W X) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessWholeSource
  rw [pascalCenteredXiMellinCanonicalVerticalSource_mirror hε τ hdet j W X,
    pascalCenteredXiMellinCanonicalTopSource_mirror hε τ hdet j W]
  simp only [map_sub, map_mul, starRingEnd_apply]
  simp
  ring

/-- The real channel of the whole source is odd and the imaginary channel is
even under the canonical mirror. -/
theorem pascalCenteredXiMellinCanonicalWholeSource_channels_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X).re =
        -(pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X).re ∧
    (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X).im =
      (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X).im := by
  have h := pascalCenteredXiMellinCanonicalWholeSource_mirror hε τ hdet j W X
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  constructor
  · simpa using hre
  · simpa using him

/-- The finite arithmetic approximant transports by complex conjugation. -/
theorem pascalCenteredXiMellinCanonicalFiniteArithmeticApproximant_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j))) W X =
      conj (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j))
        W X) := by
  rw [pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
      hε τ _ W X,
    pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
      hε τ _ W X,
    pascalCenteredXiMellinCanonicalWholeSource_mirror hε τ hdet j W X]
  simp only [map_mul, starRingEnd_apply]
  simp

/-- The finite approximant has even real channel and odd imaginary channel
under the canonical mirror.  This is a componentwise restatement of the
finite conjugation transport above, not an inequality. -/
theorem pascalCenteredXiMellinCanonicalFiniteArithmeticApproximant_channels_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j))) W X).re =
      (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j))
        W X).re ∧
    (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j))) W X).im =
      -(pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j))
        W X).im := by
  have h := pascalCenteredXiMellinCanonicalFiniteArithmeticApproximant_mirror
    hε τ hdet j W X
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  constructor
  · simpa using hre
  · simpa using him

/-! ## H7-H: normalized whole-feature integral -/

private theorem pascalCenteredXiMellinGeneralTauBoxFeature_conj
    (τ u : ℝ) (z : ℂ) :
    pascalCenteredXiMellinGeneralTauBoxFeature τ (conj z) u =
      conj (pascalCenteredXiMellinGeneralTauBoxFeature τ z u) := by
  unfold pascalCenteredXiMellinGeneralTauBoxFeature
    pascalCenteredXiMellinGeneralTauBoxKernel
  have hτ : starRingEnd ℂ ((τ : ℂ) * z) =
      (τ : ℂ) * starRingEnd ℂ z := by
    simp
  have hu : starRingEnd ℂ ((u : ℂ) * z) =
      starRingEnd ℂ z * (u : ℂ) := by
    simp
    ring
  simp only [map_div₀, map_sub, map_add, map_mul, map_ofNat,
    map_pow, Complex.conj_ofReal]
  rw [← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_conj]
  rw [hτ]
  simp only [map_mul, Complex.conj_ofReal, map_neg]

private theorem pascalCenteredXiMellinGeneralTauBoxFeature_neg_z
    (τ u : ℝ) (z : ℂ) :
    pascalCenteredXiMellinGeneralTauBoxFeature τ (-z) u =
      pascalCenteredXiMellinGeneralTauBoxFeature τ z (-u) := by
  unfold pascalCenteredXiMellinGeneralTauBoxFeature
    pascalCenteredXiMellinGeneralTauBoxKernel
  simp [mul_neg, neg_mul]
  ring

private theorem pascalCenteredXiMellinCanonicalVerticalBoxFeature_mirror_neg
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (t u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X (-t) u =
      -conj (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X t u) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature
    pascalCenteredXiMellinGeneralTauVerticalBoxFeature
  rw [pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror_fun
    hε τ hdet j]
  simp only [map_sum, map_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_neg_eq_conj,
    pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode_neg_eq_conj,
    pascalCenteredXiMellinGeneralTauBoxFeature_conj]
  simp only [starRingEnd_apply]
  ring

/-- The detailed vertical logarithmic-box feature has the same
negative-conjugation law after the finite height reflection. -/
theorem pascalCenteredXiMellinCanonicalVerticalAggregatedBoxFeature_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X u =
      -conj (pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
        τ (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X u) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
  let f : ℝ → ℂ := fun t =>
    pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
      (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
      W X t u
  have hcomp :
      (∫ t in (-W.rectangle.T)..W.rectangle.T, f (-t)) =
        ∫ t in (-W.rectangle.T)..W.rectangle.T, f t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := f)
        (a := -W.rectangle.T) (b := W.rectangle.T))
  have hcompMirror :
      (∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X (-t) u) =
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
              (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X t u := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := fun t : ℝ =>
          pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
              (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X t u)
        (a := -W.rectangle.T) (b := W.rectangle.T))
  change (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X t u) =
    -conj (∫ t in (-W.rectangle.T)..W.rectangle.T, f t)
  calc
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X (-t) u := by
      exact hcompMirror.symm
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T, -conj (f t) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      exact pascalCenteredXiMellinCanonicalVerticalBoxFeature_mirror_neg
        hε τ hdet j W X t u
    _ = -conj (∫ t in (-W.rectangle.T)..W.rectangle.T, f t) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]

private theorem pascalCenteredXiMellinCanonicalTopBoxFeature_mirror_one_sub
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (x u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W (1 - x) u =
      conj (pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W x (-u)) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
    pascalCenteredXiMellinGeneralTauTopBoxFeature
  rw [pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror_fun
    hε τ hdet j]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_one_sub_eq_neg_conj,
    pascalCenteredXiPrimeSideQuadraticizationTopNode_one_sub_eq_neg_conj,
    pascalCenteredXiMellinGeneralTauBoxFeature_neg_z,
    pascalCenteredXiMellinGeneralTauBoxFeature_conj]
  simp only [starRingEnd_apply]
  ring

/-- The top logarithmic-box feature transports by complex conjugation with
the reflected box coordinate `u ↦ -u`; the affine `x ↦ 1-x` substitution is
kept explicit. -/
theorem pascalCenteredXiMellinCanonicalTopAggregatedBoxFeature_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W u =
      conj (pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W (-u)) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
  let f : ℝ → ℂ := fun x =>
    pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
      (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
      W x (-u)
  have hcomp :
      (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), f (1 - x)) =
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ), f x := by
    simpa only [sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := W.rectangle.σ)
        (b := 1 - W.rectangle.σ) (d := 1))
  have hcompMirror :
      (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W (1 - x) u) =
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
              (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W x u := by
    simpa only [sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ =>
          pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
              (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W x u)
        (a := W.rectangle.σ) (b := 1 - W.rectangle.σ) (d := 1))
  change (∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
      pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W x u) =
    conj (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), f x)
  calc
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
            (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W (1 - x) u := by
      exact hcompMirror.symm
    _ = ∫ x in W.rectangle.σ..(1 - W.rectangle.σ), conj (f x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x hx
      exact pascalCenteredXiMellinCanonicalTopBoxFeature_mirror_one_sub
        hε τ hdet j W x u
    _ = conj (∫ x in W.rectangle.σ..(1 - W.rectangle.σ), f x) := by
      rw [intervalIntegral.intervalIntegral_conj]

/-- The actual pointwise whole-feature transport is mixed: the vertical
aggregate keeps `u`, while the top aggregate carries `u ↦ -u`. -/
theorem pascalCenteredXiMellinCanonicalWholeBoxFeature_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X u =
      -conj (pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature
        τ (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X u) -
        Complex.I * conj
          (pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
            W (-u)) := by
  unfold pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
  rw [pascalCenteredXiMellinCanonicalVerticalAggregatedBoxFeature_mirror
      hε τ hdet j W X u,
    pascalCenteredXiMellinCanonicalTopAggregatedBoxFeature_mirror
      hε τ hdet j W u]

/-- The normalized whole-feature integral has the same negative-conjugation
law as the whole source.  The nonzero-`τ` hypothesis is used only by the
existing finite logarithmic-box normalization bridge. -/
theorem pascalCenteredXiMellinCanonicalNormalizedWholeFeatureIntegral_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
              (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X u) =
      -conj (((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ
            (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
            W X u)) := by
  rw [← pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
      hε τ _ hτ W X,
    ← pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
      hε τ _ hτ W X,
    pascalCenteredXiMellinCanonicalWholeSource_mirror hε τ hdet j W X]

end DkMath.RH.CFBRCProjection
