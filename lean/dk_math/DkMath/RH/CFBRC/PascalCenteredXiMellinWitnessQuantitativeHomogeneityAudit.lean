/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessPhaseNoGoAudit
import Mathlib.Tactic

/-!
# GWSS-003C: target-specific quantitative homogeneity audit

The GWSS-002 off-critical witness is obtained by multiplying an unscaled
coordinate extractor by the scalar given by the target squared-coordinate
imaginary part.  This module exposes that factorization at the function level,
transports it through the finite zero moment and arithmetic surfaces, and
proves the corresponding first-order norm cancellation.

The resulting statement is deliberately an information audit.  Homogeneous
norm and majorant inequalities carry the same absolute scalar on both sides;
they therefore cannot by themselves extract the vanishing of the off-critical
scalar.  No nonhomogeneous estimate, positivity theorem, limit argument, or
Riemann-hypothesis consequence is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped Interval Topology

/-! ## GWSS-003C-1/2: mass witness and scalar factorization -/

/-- Scaling every coefficient of a finite Mellin witness scales the synthesized
weight pointwise by the same complex scalar. -/
theorem pascalCenteredXiMellinWitnessWeight_scaled_coefficients
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ) :
    pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i) =
      fun z => a * pascalCenteredXiMellinWitnessWeight ε τ c0 z := by
  funext z
  unfold pascalCenteredXiMellinWitnessWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A full-rank Mellin matrix yields an unscaled admissible mass extractor.

The witness is obtained from the coordinate extractor before multiplying its
coefficients by the target's imaginary displacement.  Thus this theorem does
not use an off-critical hypothesis. -/
theorem exists_pascalCenteredXiMellinMassWitness_of_full_rank_target
    {R ε : ℝ}
    (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ c0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c0) ∧
      PascalCenteredEvenWeight
        (pascalCenteredXiMellinWitnessWeight ε τ c0) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c0) R =
        pascalCenteredXiSquaredOrbitMassVec R j0 := by
  obtain ⟨c0, hc0⟩ :=
    exists_pascalCenteredXiMellinMoment_coordinate_extractor hε hdet j0
  refine ⟨c0, pascalCenteredXiMellinWitnessWeight_differentiable hε τ c0,
    pascalCenteredXiMellinWitnessWeight_even hε τ c0, ?_⟩
  rw [pascalCenteredXiMellinWitnessWeight_moment_eq]
  simpa [pascalCenteredXiMellinMomentVec] using hc0

/-- The mass extractor and its target-scaled off-critical companion can be
constructed together.  The final equality is an exact function identity, not
merely equality of their zero-side moments. -/
theorem exists_pascalCenteredXiMellinMassAndOffCriticalWitness
    {R ε : ℝ}
    (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0)
    (hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0) :
    ∃ c0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c0) ∧
      PascalCenteredEvenWeight
        (pascalCenteredXiMellinWitnessWeight ε τ c0) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c0) R =
        pascalCenteredXiSquaredOrbitMassVec R j0 ∧
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ
        (fun i => (pascalCenteredXiSquaredOrbitCoordinate R j0).im * c0 i)) ∧
      PascalCenteredEvenWeight
        (pascalCenteredXiMellinWitnessWeight ε τ
          (fun i => (pascalCenteredXiSquaredOrbitCoordinate R j0).im * c0 i)) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ
            (fun i => (pascalCenteredXiSquaredOrbitCoordinate R j0).im * c0 i)) R =
        ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
          pascalCenteredXiSquaredOrbitMassVec R j0 ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ
            (fun i => (pascalCenteredXiSquaredOrbitCoordinate R j0).im * c0 i)) R ≠ 0 ∧
      pascalCenteredXiMellinWitnessWeight ε τ
          (fun i => (pascalCenteredXiSquaredOrbitCoordinate R j0).im * c0 i) =
        fun z => (pascalCenteredXiSquaredOrbitCoordinate R j0).im *
          pascalCenteredXiMellinWitnessWeight ε τ c0 z := by
  obtain ⟨c0, hdiff, heven, hmoment⟩ :=
    exists_pascalCenteredXiMellinMassWitness_of_full_rank_target hε hdet j0
  let qIm : ℂ := (pascalCenteredXiSquaredOrbitCoordinate R j0).im
  have hdiff_scaled := pascalCenteredXiMellinWitnessWeight_differentiable
    hε τ (fun i => qIm * c0 i)
  have heven_scaled := pascalCenteredXiMellinWitnessWeight_even
    hε τ (fun i => qIm * c0 i)
  have hscale := pascalCenteredXiMellinWitnessWeight_scaled_coefficients
    qIm ε τ c0
  have hmoment_scaled :
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ
            (fun i => qIm * c0 i)) R =
        qIm * pascalCenteredXiSquaredOrbitMassVec R j0 := by
    rw [pascalCenteredXiMellinWitnessWeight_moment_eq]
    calc
      ∑ i, qIm * c0 i *
          pascalCenteredXiZeroDiskWeightedMoment
            (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) R =
          qIm * ∑ i, c0 i *
            pascalCenteredXiZeroDiskWeightedMoment
              (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = qIm * pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c0) R := by
        rw [pascalCenteredXiMellinWitnessWeight_moment_eq]
      _ = qIm * pascalCenteredXiSquaredOrbitMassVec R j0 := by
        rw [hmoment]
  have hq : qIm ≠ 0 := by
    dsimp [qIm]
    exact Complex.ofReal_ne_zero.mpr hoff
  have hmoment_scaled_ne :
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ
            (fun i => qIm * c0 i)) R ≠ 0 := by
    rw [hmoment_scaled]
    exact mul_ne_zero hq hmass
  refine ⟨c0, hdiff, heven, hmoment, hdiff_scaled, heven_scaled,
    ?_, hmoment_scaled_ne, ?_⟩
  · simpa [qIm] using hmoment_scaled
  · simpa [qIm] using hscale

/-! ## GWSS-003C-3: arithmetic scaling transport -/

/-- The ordinary-zeta right-edge integral has the same scalar factor as the
finite Mellin witness weight. -/
theorem pascalCenteredXiMellinWitnessOrdinaryZetaRightEdgeIntegral_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (σ T : ℝ) :
    pascalXiOrdinaryZetaRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) σ T =
      a * pascalXiOrdinaryZetaRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ c0) σ T := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  unfold pascalXiOrdinaryZetaRightEdgeIntegral
    pascalXiOrdinaryZetaRightEdgeIntegrand
  rw [show
      (fun t : ℝ =>
        (a * pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
          pascalXiOrdinaryZetaNegLogDeriv
            (pascalSymmetricRectangleRightEdge σ t)) * Complex.I) =
      (fun t : ℝ => a *
        ((pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
          pascalXiOrdinaryZetaNegLogDeriv
            (pascalSymmetricRectangleRightEdge σ t)) * Complex.I)) by
        funext t
        ring]
  exact intervalIntegral.integral_const_mul a _

/-- The archimedean right-edge integral is first-order homogeneous in the
finite Mellin witness weight. -/
theorem pascalCenteredXiMellinWitnessArchimedeanRightEdgeIntegral_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (σ T : ℝ) :
    pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) σ T =
      a * pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ c0) σ T := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  unfold pascalXiArchimedeanRightEdgeIntegral
    pascalXiArchimedeanRightEdgeIntegrand
  rw [show
      (fun t : ℝ =>
        (a * pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
          pascalXiArchimedeanLogDeriv
            (pascalSymmetricRectangleRightEdge σ t)) * Complex.I) =
      (fun t : ℝ => a *
        ((pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
          pascalXiArchimedeanLogDeriv
            (pascalSymmetricRectangleRightEdge σ t)) * Complex.I)) by
        funext t
        ring]
  exact intervalIntegral.integral_const_mul a _

/-- The elementary right-edge integral is first-order homogeneous in the
finite Mellin witness weight. -/
theorem pascalCenteredXiMellinWitnessElementaryRightEdgeIntegral_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (σ T : ℝ) :
    pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) σ T =
      a * pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinWitnessWeight ε τ c0) σ T := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  unfold pascalXiElementaryRightEdgeIntegral
    pascalXiElementaryRightEdgeIntegrand
  rw [show
      (fun t : ℝ =>
        (a * pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
          pascalXiElementaryLogDerivCorrection
            (pascalSymmetricRectangleRightEdge σ t)) * Complex.I) =
      (fun t : ℝ => a *
        ((pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
          pascalXiElementaryLogDerivCorrection
            (pascalSymmetricRectangleRightEdge σ t)) * Complex.I)) by
        funext t
        ring]
  exact intervalIntegral.integral_const_mul a _

/-- The top-horizontal contribution is first-order homogeneous; this is a
finite-height identity and makes no horizontal-decay claim. -/
theorem pascalCenteredXiMellinWitnessTopHorizontalContribution_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) W =
      a * pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinWitnessWeight ε τ c0) W := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  unfold pascalCenteredXiTopHorizontalContribution
    pascalCenteredXiWeightedNegLogDeriv
  rw [show
      (fun u : ℝ =>
        a * pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalCenteredXiNegLogDeriv
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.rectangle.T))) =
      (fun u : ℝ => a *
        (pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          pascalCenteredXiNegLogDeriv
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)))) by
        funext u
        ring]
  exact intervalIntegral.integral_const_mul a _

/-- The complete finite arithmetic RHS has the same target scalar factor as
the synthesized witness. -/
theorem pascalCenteredXiMellinWitnessFiniteArithmeticRHS_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiFiniteArithmeticRHS
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) W =
      a * pascalCenteredXiFiniteArithmeticRHS
        (pascalCenteredXiMellinWitnessWeight ε τ c0) W := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  exact pascalCenteredXiFiniteArithmeticRHS_const_mul a
    (pascalCenteredXiMellinWitnessWeight ε τ c0) W

/-! ## GWSS-003C-4: norm homogeneity and cancellation -/

/-- A nonzero complex scalar can be cancelled from a first-order norm bound. -/
theorem norm_mul_le_norm_mul_iff_of_ne_zero
    {a w : ℂ} {B : ℝ} (ha : a ≠ 0) :
    ‖a * w‖ ≤ ‖a‖ * B ↔ ‖w‖ ≤ B := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  constructor
  · intro h
    apply le_of_mul_le_mul_left (a := ‖a‖) ?_ ha_norm
    simpa [norm_mul] using h
  · intro h
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h (le_of_lt ha_norm)

/-- The prime cutoff integrand scales pointwise by the same complex scalar. -/
theorem pascalPrimePowerRightEdgeCutoffIntegrand_witness_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (σ : ℝ) (X : ℕ) (t : ℝ) :
    pascalPrimePowerRightEdgeCutoffIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) σ X t =
      a * pascalPrimePowerRightEdgeCutoffIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ c0) σ X t := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients]
  unfold pascalPrimePowerRightEdgeCutoffIntegrand
  ring

/-- The existing vertical prime majorant remains valid after scaling, with the
same absolute scalar on both the integrand and weight sides. -/
theorem norm_pascalPrimePowerRightEdgeCutoffIntegrand_witness_le_scaled_majorant
    {n : ℕ} {a : ℂ} {ε : ℝ} {τ : Fin n → ℝ} {c0 : Fin n → ℂ}
    {σ : ℝ} (hσ : 1 < σ) (X : ℕ) (t : ℝ) :
    ‖pascalPrimePowerRightEdgeCutoffIntegrand
        (pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)) σ X t‖ ≤
      ‖a‖ *
        (‖pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t))‖ *
          pascalVonMangoldtVerticalMajorant σ) := by
  rw [pascalPrimePowerRightEdgeCutoffIntegrand_witness_const_mul, norm_mul]
  have hprime := norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant
    hσ X t
  have hbase :
      ‖pascalPrimePowerRightEdgeCutoffIntegrand
          (pascalCenteredXiMellinWitnessWeight ε τ c0) σ X t‖ ≤
        ‖pascalCenteredXiMellinWitnessWeight ε τ c0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge σ t))‖ *
          pascalVonMangoldtVerticalMajorant σ := by
    calc
      ‖pascalPrimePowerRightEdgeCutoffIntegrand
          (pascalCenteredXiMellinWitnessWeight ε τ c0) σ X t‖ =
          ‖pascalCenteredXiMellinWitnessWeight ε τ c0
              (pascalOrdinaryToCentered
                (pascalSymmetricRectangleRightEdge σ t))‖ *
            ‖pascalPrimePowerPHZFiniteUpTo X
              (pascalSymmetricRectangleRightEdge σ t)‖ := by
        unfold pascalPrimePowerRightEdgeCutoffIntegrand
        rw [norm_mul, norm_mul]
        norm_num
      _ ≤ ‖pascalCenteredXiMellinWitnessWeight ε τ c0
              (pascalOrdinaryToCentered
                (pascalSymmetricRectangleRightEdge σ t))‖ *
            pascalVonMangoldtVerticalMajorant σ := by
        exact mul_le_mul_of_nonneg_left hprime (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left hbase (norm_nonneg _)

/-- The right side of the prime majorant itself has exact absolute scalar
homogeneity. -/
theorem norm_pascalCenteredXiMellinWitness_mul_majorant_const_mul
    {n : ℕ} (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ)
    (σ t : ℝ) :
    ‖pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i)
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge σ t))‖ *
        pascalVonMangoldtVerticalMajorant σ =
      ‖a‖ *
        (‖pascalCenteredXiMellinWitnessWeight ε τ c0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t))‖ *
          pascalVonMangoldtVerticalMajorant σ) := by
  rw [pascalCenteredXiMellinWitnessWeight_scaled_coefficients, norm_mul]
  ring

/-! ## GWSS-003C-5/6: normalized audit conclusion -/

/-- The off-critical scalar cancels from the finite explicit formula once its
nonzero factorization is compared with the mass witness.  The conclusion is
the mass identity, not a contradiction and not an independent estimate. -/
theorem pascalCenteredXiFiniteArithmeticRHS_mass_identity_of_scaled_witness
    {W : PascalCenteredXiResidueTransportWindow}
    {h hOff : ℂ → ℂ} {q m : ℂ}
    (hhOff : Differentiable ℂ hOff)
    (hevenOff : PascalCenteredEvenWeight hOff)
    (hq : q ≠ 0)
    (hscale : hOff = fun z => q * h z)
    (hmomentOff : pascalCenteredXiZeroDiskWeightedMoment hOff W.R = q * m) :
    pascalCenteredXiFiniteArithmeticRHS h W =
      -(2 * Real.pi * Complex.I) * m := by
  have hlinear :
      pascalCenteredXiFiniteArithmeticRHS hOff W =
        q * pascalCenteredXiFiniteArithmeticRHS h W := by
    rw [hscale]
    exact pascalCenteredXiFiniteArithmeticRHS_const_mul q h W
  have hexplicit := pascalCenteredXiFiniteArithmeticRHS_eq_zeroMoment_factor
    hhOff hevenOff W
  rw [hmomentOff] at hexplicit
  have hcancel :
      q * pascalCenteredXiFiniteArithmeticRHS h W =
        q * (-(2 * Real.pi * Complex.I) * m) := by
    calc
      q * pascalCenteredXiFiniteArithmeticRHS h W =
          pascalCenteredXiFiniteArithmeticRHS hOff W := hlinear.symm
      _ = -(2 * Real.pi * Complex.I) * (q * m) := hexplicit
      _ = q * (-(2 * Real.pi * Complex.I) * m) := by ring
  exact (mul_left_cancel₀ hq hcancel)

end DkMath.RH.CFBRCProjection
