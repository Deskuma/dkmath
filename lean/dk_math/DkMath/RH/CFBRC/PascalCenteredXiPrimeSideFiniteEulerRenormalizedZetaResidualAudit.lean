/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFinitePotentialRectangleScalarMismatchAudit
import DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# CS30: finite Euler-renormalized zeta residual audit

This file keeps the CS30 construction finite.  The rectangle background and
the reach classification are exact scalar consequences of the preceding
ledger.  The Euler potential is a finite sum over the canonical prime-power
pair support; it is not an infinite Euler product or an infinite logarithmic
derivative expansion.
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

/-! ## CS30-A: complement boundary and finite rectangle telescope -/

noncomputable def pascalCenteredXiPrimeSideFiniteComplementBoundaryScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    (pascalCenteredXiPrimeSideFiniteLeftCompanion ε W X +
      pascalCenteredXiPrimeSideFiniteBottomCompanion ε W X)).re

theorem pascalCenteredXiPrimeSideFiniteNormalizedPrime_add_topArithmetic
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X +
        pascalCenteredXiPrimeSideFiniteTopArithmeticCompanionScalar ε W X =
      -pascalCenteredXiPrimeSideFiniteComplementBoundaryScalar ε W X := by
  have ht := pascalCenteredXiPrimeSideFiniteRectangleCompanions_telescope ε W X
  have hn :=
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateInteraction_div_pi
      hε W X
  have hr := pascalCenteredXiPrimeSideFiniteRightCompanion_normalized_re_eq_interaction_div_pi
    hε W X
  have hrt :
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X =
        (((2 * Real.pi * Complex.I)⁻¹) *
          pascalCenteredXiPrimeSideFiniteRightCompanion ε W X).re := by
    rw [hn, hr]
  have hproj := congrArg
    (fun z : ℂ => ((2 * Real.pi * Complex.I)⁻¹ * z).re) ht
  have hproj' :
      (((2 * Real.pi * Complex.I)⁻¹) *
          pascalCenteredXiPrimeSideFiniteRightCompanion ε W X).re +
        (((2 * Real.pi * Complex.I)⁻¹) *
          pascalCenteredXiPrimeSideFiniteTopCompanion ε W X).re +
        (((2 * Real.pi * Complex.I)⁻¹) *
          (pascalCenteredXiPrimeSideFiniteLeftCompanion ε W X +
            pascalCenteredXiPrimeSideFiniteBottomCompanion ε W X)).re = 0 := by
    simpa only [mul_add, Complex.add_re, mul_zero, Complex.zero_re,
      add_assoc] using hproj
  unfold pascalCenteredXiPrimeSideFiniteTopArithmeticCompanionScalar
    pascalCenteredXiPrimeSideFiniteComplementBoundaryScalar
  rw [hrt]
  linarith

/-! ## CS30-B: the finite background -/

noncomputable def pascalCenteredXiPrimeSideFiniteRectangleBackground
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R +
    pascalCenteredXiPrimeSideFiniteComplementBoundaryScalar ε W X -
    pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W -
    pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W -
    2 * pascalCenteredXiPrimeSideFiniteTopArchimedeanCompanionScalar ε W -
    2 * pascalCenteredXiPrimeSideFiniteTopElementaryCompanionScalar ε W

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_mismatch
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
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      Real.pi *
        (pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
          pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X) := by
  have hG := pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
    hε W X
  have hTop := pascalCenteredXiPrimeSideFiniteNormalizedTopLedger
    hε hSafe hZeta hArch hElem X
  have hT := pascalCenteredXiPrimeSideFiniteNormalizedPrime_add_topArithmetic hε W X
  unfold pascalCenteredXiPrimeSideIndependentCompleteSourceReal at hG
  unfold pascalCenteredXiPrimeSideFiniteRectangleBackground
  have hTop' :
      pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W =
        (((2 * Real.pi * Complex.I)⁻¹) *
          pascalCenteredXiPrimeSideFiniteTopCompanion ε W X).re +
        (((2 * Real.pi * Complex.I)⁻¹) *
          (2 * pascalCenteredXiPrimeSideTopArchimedeanContribution ε W)).re +
        (((2 * Real.pi * Complex.I)⁻¹) *
          (2 * pascalCenteredXiPrimeSideTopElementaryContribution ε W)).re +
        pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X := by
    unfold pascalCenteredXiPrimeSideFiniteNormalizedTopContribution at hTop
    exact hTop
  rw [hTop'] at hG
  unfold pascalCenteredXiPrimeSideFiniteTopArithmeticCompanionScalar at hT
  unfold pascalCenteredXiPrimeSideFiniteTopArchimedeanCompanionScalar
    pascalCenteredXiPrimeSideFiniteTopElementaryCompanionScalar
  have hdouble (z : ℂ) :
      (((2 * Real.pi * Complex.I)⁻¹) * (2 * z)).re =
        2 * (((2 * Real.pi * Complex.I)⁻¹) * z).re := by
    simp [Complex.mul_re]
    ring
  rw [hdouble, hdouble] at hG
  linear_combination hG - Real.pi * hT

/-! ## CS30-C: mismatch reach classification -/

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_mismatch_ge_shifted_background
    {ε η : ℝ} (hε : 0 < ε)
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
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ η ↔
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X - η / Real.pi ≤
        pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X := by
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_mismatch
    hε hSafe hZeta hArch hElem X]
  constructor <;> intro h
  · have hp : 0 < Real.pi := Real.pi_pos
    have h' :
        pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
            pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X ≤
          η / Real.pi :=
      (le_div_iff₀ hp).2 (by simpa [mul_comm] using h)
    linarith
  · have hp : 0 < Real.pi := Real.pi_pos
    have h' :
        pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
            pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X ≤
          η / Real.pi := by
      linarith
    have h'' := (le_div_iff₀ hp).1 h'
    simpa [mul_comm] using h''

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonpos_iff_background_le_mismatch
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
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 ↔
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X ≤
        pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X := by
  simpa using pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_mismatch_ge_shifted_background
    hε hSafe hZeta hArch hElem X (η := 0)

theorem pascalCenteredXiPrimeSideFiniteMismatch_zero_need_not_imply_contact :
    ∃ B G : ℝ, 0 < B ∧ G = Real.pi * (B - 0) ∧ ¬ G ≤ 0 := by
  refine ⟨1, Real.pi, by norm_num, ?_, ?_⟩
  · ring
  · exact not_le_of_gt Real.pi_pos

theorem pascalCenteredXiPrimeSideFinitePositiveMismatch_can_force_contact :
    ∃ B M G : ℝ, 0 < B ∧ 0 < M ∧ G = Real.pi * (B - M) ∧ G ≤ 0 := by
  refine ⟨1, 2, -Real.pi, by norm_num, by norm_num, ?_, ?_⟩
  · ring
  · linarith [Real.pi_pos]

/-! ## CS30-D: finite Euler potential and a useful bonus normalisation -/

noncomputable def pascalCenteredXiPrimeSideFiniteEulerLogPotential
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    (((pk.2 + 1 : ℕ) : ℂ)⁻¹) *
      eulerPrimePowerMode pk.1 (pk.2 + 1) s

noncomputable def pascalCenteredXiPrimeSideFiniteEulerCompensator
    (X : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-pascalCenteredXiPrimeSideFiniteEulerLogPotential X s)

noncomputable def pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual
    (X : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * pascalCenteredXiPrimeSideFiniteEulerCompensator X s

@[simp] theorem pascalCenteredXiPrimeSideFiniteEulerLogPotential_zero (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerLogPotential 0 s = 0 := by
  simp [pascalCenteredXiPrimeSideFiniteEulerLogPotential,
    pascalPrimePowerPairSupportUpTo, pascalPrimeCoordinateSupportUpTo]

@[simp] theorem pascalCenteredXiPrimeSideFiniteEulerLogPotential_one (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerLogPotential 1 s = 0 := by
  unfold pascalCenteredXiPrimeSideFiniteEulerLogPotential
  apply Finset.sum_eq_zero
  intro pk hpk
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
  have hp : Nat.Prime pk.1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hp_le : pk.1 ≤ 1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).2
  exfalso
  exact (Nat.not_le_of_lt hp.one_lt) hp_le

@[simp] theorem pascalCenteredXiPrimeSideFiniteEulerCompensator_zero (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerCompensator 0 s = 1 := by
  simp [pascalCenteredXiPrimeSideFiniteEulerCompensator]

@[simp] theorem pascalCenteredXiPrimeSideFiniteEulerCompensator_one (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerCompensator 1 s = 1 := by
  simp [pascalCenteredXiPrimeSideFiniteEulerCompensator]

theorem pascalCenteredXiPrimeSideFiniteEulerCompensator_ne_zero
    (X : ℕ) (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerCompensator X s ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_zero
    (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual 0 s = riemannZeta s := by
  simp [pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual]

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_one
    (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual 1 s = riemannZeta s := by
  simp [pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual]

/-! A termwise derivative certificate for the finite Euler potential. -/

theorem eulerPrimePowerMode_hasDerivAt_neg_log_mul
    {p j : ℕ} (hp : Nat.Prime p) (_hj : 0 < j) (s : ℂ) :
    HasDerivAt (fun z : ℂ => eulerPrimePowerMode p j z)
      (-((j : ℂ) * (Real.log (p : ℝ) : ℂ) *
        eulerPrimePowerMode p j s)) s := by
  have hbase : (((p ^ j : ℕ) : ℂ) ≠ 0) := by
    exact_mod_cast (pow_ne_zero j hp.ne_zero)
  have hpow :=
    (hasDerivAt_neg (x := s)).const_cpow (c := ((p ^ j : ℕ) : ℂ))
      (Or.inl hbase)
  have hlog : Complex.log ((p ^ j : ℕ) : ℂ) =
      (j : ℂ) * (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.natCast_log]
    norm_num [Nat.cast_pow, Real.log_pow]
  rw [eulerPrimePowerMode_eq_primePower_cpow_neg hp]
  convert hpow using 1
  · ext z
    rw [eulerPrimePowerMode_eq_primePower_cpow_neg hp]
  · rw [hlog]
    ring

theorem pascalCenteredXiPrimeSideFiniteEulerLogPotential_hasDerivAt
    (X : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ =>
      pascalCenteredXiPrimeSideFiniteEulerLogPotential X z)
      (-pascalPrimePowerPHZFiniteUpTo X s) s := by
  classical
  unfold pascalCenteredXiPrimeSideFiniteEulerLogPotential
  have hsum : HasDerivAt
      (∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        fun z : ℂ => (((pk.2 + 1 : ℕ) : ℂ)⁻¹) *
          eulerPrimePowerMode pk.1 (pk.2 + 1) z)
      (∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        -((pk.2 + 1 : ℕ) : ℂ)⁻¹ *
          ((pk.2 + 1 : ℂ) * (Real.log (pk.1 : ℝ) : ℂ) *
            eulerPrimePowerMode pk.1 (pk.2 + 1) s)) s := by
    apply HasDerivAt.sum
    intro pk hpk
    have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
    have hp : Nat.Prime pk.1 :=
      (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
    have hj : 0 < pk.2 + 1 := by omega
    have hmode := eulerPrimePowerMode_hasDerivAt_neg_log_mul hp hj s
    convert hmode.const_mul (((pk.2 + 1 : ℕ) : ℂ)⁻¹) using 1
    · rfl
    · simp only [Nat.cast_add, Nat.cast_one]
      ring
  convert hsum using 1
  · funext z
    simp only [Finset.sum_apply]
  · rw [pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro pk hpk
    have hj : (pk.2 + 1 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero pk.2)
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [hj]

/-! ## CS30-E: the finite compensator log derivative -/

theorem pascalCenteredXiPrimeSideFiniteEulerCompensator_hasDerivAt
    (X : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ =>
      pascalCenteredXiPrimeSideFiniteEulerCompensator X z)
      (pascalPrimePowerPHZFiniteUpTo X s *
        pascalCenteredXiPrimeSideFiniteEulerCompensator X s) s := by
  unfold pascalCenteredXiPrimeSideFiniteEulerCompensator
  have hA := pascalCenteredXiPrimeSideFiniteEulerLogPotential_hasDerivAt X s
  have hneg := hA.neg
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasDerivAt_exp
      (-pascalCenteredXiPrimeSideFiniteEulerLogPotential X s)).comp s hneg

theorem pascalCenteredXiPrimeSideFiniteEulerCompensator_logDeriv
    (X : ℕ) (s : ℂ) :
    logDeriv (fun z : ℂ =>
      pascalCenteredXiPrimeSideFiniteEulerCompensator X z) s =
      pascalPrimePowerPHZFiniteUpTo X s := by
  have hcomp := pascalCenteredXiPrimeSideFiniteEulerCompensator_hasDerivAt X s
  rw [logDeriv_apply, hcomp.deriv]
  field_simp [pascalCenteredXiPrimeSideFiniteEulerCompensator_ne_zero X s]

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
    {X : ℕ} {s : ℂ} (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    -logDeriv (fun z : ℂ =>
      pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z) s =
      pascalXiOrdinaryZetaNegLogDeriv s -
        pascalPrimePowerPHZFiniteUpTo X s := by
  have hcomp := pascalCenteredXiPrimeSideFiniteEulerCompensator_hasDerivAt X s
  have hmul := logDeriv_mul s hzeta
    (pascalCenteredXiPrimeSideFiniteEulerCompensator_ne_zero X s)
    (differentiableAt_riemannZeta hs1) hcomp.differentiableAt
  rw [show (fun z : ℂ =>
      pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z) =
      (fun z : ℂ => riemannZeta z *
        pascalCenteredXiPrimeSideFiniteEulerCompensator X z) by rfl]
  rw [hmul, pascalCenteredXiPrimeSideFiniteEulerCompensator_logDeriv]
  unfold pascalXiOrdinaryZetaNegLogDeriv
  simp only [logDeriv_apply, div_eq_mul_inv]
  ring

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_ne_zero
    {X : ℕ} {s : ℂ} (hzeta : riemannZeta s ≠ 0) :
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X s ≠ 0 := by
  exact mul_ne_zero hzeta
    (pascalCenteredXiPrimeSideFiniteEulerCompensator_ne_zero X s)

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_ne_zero_on_safe_top
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) ≠ 0 := by
  dsimp [IsPascalCenteredXiTopLogDerivDecompositionSafe] at hSafe
  exact pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_ne_zero
    (hSafe u hu).2.2.1

/-! ## CS30-F: the finite top mismatch is one residual integral -/

theorem pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_two_residual_integral
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X =
      2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
  unfold pascalCenteredXiPrimeSideTopZetaCutoffMismatch
  rw [← mul_sub, ← intervalIntegral.integral_sub hZeta hPHZ]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hsafe := hSafe u hu
  dsimp [IsPascalCenteredXiTopLogDerivDecompositionSafe] at hsafe
  have hres :=
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
      (X := X) (s := pascalSymmetricRectangleTopEdge u W.rectangle.T)
      hsafe.2.1 hsafe.2.2.1
  dsimp
  rw [hres]
  ring

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_residual_integral_im_div_two_pi
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (2 * ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          (-logDeriv (fun z : ℂ =>
            pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
            (pascalSymmetricRectangleTopEdge u W.rectangle.T))).im /
        (2 * Real.pi) := by
  unfold pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar
  rw [normalized_by_two_pi_i_re]
  rw [pascalCenteredXiPrimeSideTopZetaCutoffMismatch_eq_two_residual_integral
    hSafe hZeta hPHZ]


/-! The remaining derivative/log-derivative bridge is deliberately named. -/

inductive PascalCenteredXiPrimeSideFiniteEulerResidualScalarReachGap : Prop
  | no_independent_finite_euler_residual_scalar_reach_estimate

end DkMath.RH.CFBRCProjection
