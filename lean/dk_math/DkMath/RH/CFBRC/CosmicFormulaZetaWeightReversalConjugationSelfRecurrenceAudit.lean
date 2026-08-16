/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaMirrorBaselineFunctionalReflectionHeightReversalAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit"

/-!
# CFZP-013: weight-reversal conjugation and ray self-recurrence audit

This module closes the finite conjugation layer left explicit by CFZP-012.
The `τ = 0` Mellin weight and positive natural modes are conjugation-compatible,
so the finite right ray reverses to the conjugate right ray.  The remaining
weight mismatch is isolated as a pure-imaginary skew correction.  The
functional-reflection contribution and its interference are intentionally not
collapsed.

No infinite cutoff, sign provider, baseline collapse, phase branch, or RH
consequence is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open scoped BigOperators ComplexConjugate Interval Topology

/-! ## Gate A: Mellin weight conjugation -/

/-- The fixed `τ = 0` Mellin weight commutes with complex conjugation. -/
theorem cfzp013MellinWeight_conj
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0 (conj z) =
      conj (pascalCenteredXiMellinSecondDifferenceWeight ε 0 z) := by
  rw [pascalCenteredXiMellinQuadraticWeight_eq_generic hε,
    pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
  unfold mellinQuadraticBoxWeight
  rw [map_mul, map_pow, mellinQuadraticBoxMultiplier_conj hε]

/-- Along the finite right edge, reversing height conjugates the Mellin weight. -/
theorem cfzp013MellinWeight_rightEdge_neg_eq_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalCenteredXiPrimeSideModePhaseNode W (-t)) =
      conj (pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalCenteredXiPrimeSideModePhaseNode W t)) := by
  rw [cfzp012ModePhaseNode_neg_eq_conj W t,
    cfzp013MellinWeight_conj hε]

/-! ## Gate B: positive natural mode conjugation -/

/-- A positive prime-power mode reverses height by complex conjugation. -/
theorem cfzp013PrimePowerMode_rightEdge_neg_eq_conj
    {p k : ℕ} (_hp : Nat.Prime p)
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    (((p ^ (k + 1) : ℕ) : ℂ) ^
        (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)))) =
      conj (((p ^ (k + 1) : ℕ) : ℂ) ^
        (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))) := by
  have hcoord : pascalSymmetricRectangleRightEdge W.rectangle.σ (-t) =
      conj (pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    apply Complex.ext <;>
      simp [pascalSymmetricRectangleRightEdge]
  have harg : ((p ^ (k + 1) : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  rw [hcoord]
  have hcpow := Complex.cpow_conj
    ((p ^ (k + 1) : ℕ) : ℂ)
    (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)) harg
  simpa using hcpow

/-! ## Gate C: source summand and finite ray conjugation -/

/-- The actual finite source summand reverses to its conjugate. -/
theorem cfzp013RightSourceSummand_neg_eq_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k (-t) =
      conj (pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t) := by
  unfold pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
  rw [cfzp013MellinWeight_rightEdge_neg_eq_conj hε W t,
    cfzp013PrimePowerMode_rightEdge_neg_eq_conj hp W t]
  simp only [map_mul]

/-- The finite right ray is self-recurrent under height reversal and conjugation. -/
theorem cfzp013FinitePrimePowerRayAmplitude_neg_eq_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t) =
      conj (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t) := by
  unfold pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact cfzp013RightSourceSummand_neg_eq_conj hε W hp t

/-! ## Gate D: the weight-skew correction -/

/-- The Mellin weight mismatch after height reversal. -/
noncomputable def cfzp013WeightConjugationSkew
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) -
    conj (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t))

/-- The skew correction is anti-self-conjugate. -/
theorem cfzp013WeightConjugationSkew_conj_eq_neg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    conj (cfzp013WeightConjugationSkew ε W t) =
      -cfzp013WeightConjugationSkew ε W t := by
  unfold cfzp013WeightConjugationSkew
  simp

/-- The skew correction has zero real part. -/
theorem cfzp013WeightConjugationSkew_re_eq_zero
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    (cfzp013WeightConjugationSkew ε W t).re = 0 := by
  unfold cfzp013WeightConjugationSkew
  simp

/-- The skew is twice the imaginary component of the Mellin weight. -/
theorem cfzp013WeightConjugationSkew_eq_two_mul_I_mul_im
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    cfzp013WeightConjugationSkew ε W t =
      2 * Complex.I *
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t)).im := by
  unfold cfzp013WeightConjugationSkew
  apply Complex.ext
  all_goals simp <;> ring

/-- The finite bare reversed-mode sum used by the correction term. -/
noncomputable def cfzp013BareReversedModeSum
    (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
    (((p ^ (k + 1) : ℕ) : ℂ) ^
      (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))))

/-- The CFZP-012 correction is exactly skew times the finite bare mode sum. -/
theorem cfzp013ReweightedReversedRightRay_sub_actualRightRayAtNeg_eq_skew_mul_bareSum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    cfzp012ReweightedReversedRightPrimePowerRayAmplitude ε W X p t -
        pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t) =
      cfzp013WeightConjugationSkew ε W t *
        cfzp013BareReversedModeSum W X p t := by
  rw [cfzp012ReweightedReversedRightRay_sub_actualRightRayAtNeg_eq_weightCorrection]
  unfold cfzp013BareReversedModeSum cfzp013WeightConjugationSkew
  simp_rw [← cfzp013MellinWeight_rightEdge_neg_eq_conj hε W t]
  rw [Finset.mul_sum]

/-! ## Gate E: self-recurrent mirror baseline residual -/

/-- The mirror baseline residual contains a functional contribution, the
conjugate of the original right-ray residual, and the explicit skew correction. -/
theorem cfzp013SameHeightMirrorRay_sub_one_eq_functional_add_conjRightResidual_add_skew
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t - 1 =
      cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
        (conj (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t) - 1) +
        cfzp013WeightConjugationSkew ε W t *
          cfzp013BareReversedModeSum W X p t := by
  have hbase :=
    cfzp012SameHeightMirrorRay_sub_one_eq_functionalReflection_add_reversedRightResidual
      ε W X p t
  have hcorr :=
    cfzp013ReweightedReversedRightRay_sub_actualRightRayAtNeg_eq_skew_mul_bareSum
      hε W X p t
  have hright := cfzp013FinitePrimePowerRayAmplitude_neg_eq_conj
    hε W (X := X) (p := p) hp t
  calc
    cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t - 1 =
        cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
          (cfzp012ReweightedReversedRightPrimePowerRayAmplitude ε W X p t - 1) :=
      hbase
    _ = cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
          ((cfzp012ReweightedReversedRightPrimePowerRayAmplitude ε W X p t -
              pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t)) +
            (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t) - 1)) := by
      ring
    _ = cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
          (cfzp013WeightConjugationSkew ε W t *
              cfzp013BareReversedModeSum W X p t +
            (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t) - 1)) := by
      rw [hcorr]
    _ = cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
          (conj (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t) - 1) +
        cfzp013WeightConjugationSkew ε W t *
          cfzp013BareReversedModeSum W X p t := by
      rw [hright]
      ring

/-- Conjugating the right-ray residual preserves its `Complex.normSq`. -/
theorem cfzp013ConjRightRayResidual_normSq_eq
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    Complex.normSq
        (conj (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t) - 1) =
      Complex.normSq
        (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t - 1) := by
  simpa only [map_sub, map_one] using
    (Complex.normSq_conj
      (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t - 1))

/-! ## Gate F: remaining interference frontier -/

/-- The remaining closure needs functional/skew/interference transport. -/
inductive Cfzp013FunctionalReflectionSkewInterferenceClosureGap : Prop
  | noFunctionalReflectionSkewInterferenceClosureProvider

end DkMath.RH.CFBRCProjection
