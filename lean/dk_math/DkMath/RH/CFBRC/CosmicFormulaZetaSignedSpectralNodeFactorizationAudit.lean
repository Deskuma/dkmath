/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaOffDiagonalPairGramAudit
import DkMath.Analysis.MellinQuadraticGramKernel
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSignedSpectralNodeFactorizationAudit"

/-!
# CFZP-006E: signed spectral-node factorization audit

This module lifts one positive prime-power mode to the two signed spectral
nodes `+log q` and `-log q` used by the Mellin feature map.  The minus sign is
carried by the negative node itself; the minus-node coefficient is therefore
defined without an additional sign.

Only the per-mode two-node feature and its fixed-box Gram energy are closed.
No finite-support flattening, full-source Gram identification, completion
remainder bridge, or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Horizontal real shifts -/

noncomputable def cfzpHorizontalRealShift (s : ℂ) (τ : ℝ) : ℂ :=
  s + (τ : ℂ)

@[simp] theorem cfzpHorizontalRealShift_re (s : ℂ) (τ : ℝ) :
    (cfzpHorizontalRealShift s τ).re = s.re + τ := by
  simp [cfzpHorizontalRealShift]

@[simp] theorem cfzpHorizontalRealShift_im (s : ℂ) (τ : ℝ) :
    (cfzpHorizontalRealShift s τ).im = s.im := by
  simp [cfzpHorizontalRealShift]

theorem centeredSigma_cfzpHorizontalRealShift (s : ℂ) (τ : ℝ) :
    centeredSigma (cfzpHorizontalRealShift s τ).re =
      centeredSigma s.re + τ := by
  simp only [cfzpHorizontalRealShift_re]
  unfold centeredSigma
  ring

theorem primeMirrorRightAmplitude_cfzpHorizontalRealShift
    (q : ℕ) (s : ℂ) (τ : ℝ) :
    primeMirrorRightAmplitude q (centeredSigma (cfzpHorizontalRealShift s τ).re) =
      primeMirrorRightAmplitude q (centeredSigma s.re) *
        Real.exp (τ * Real.log (q : ℝ)) := by
  rw [centeredSigma_cfzpHorizontalRealShift]
  unfold primeMirrorRightAmplitude
  have harg :
      (centeredSigma s.re + τ) * Real.log (q : ℝ) =
        centeredSigma s.re * Real.log (q : ℝ) +
          τ * Real.log (q : ℝ) := by
    ring
  rw [harg]
  rw [Real.exp_add]

theorem primeMirrorLeftAmplitude_cfzpHorizontalRealShift
    (q : ℕ) (s : ℂ) (τ : ℝ) :
    primeMirrorLeftAmplitude q (centeredSigma (cfzpHorizontalRealShift s τ).re) =
      primeMirrorLeftAmplitude q (centeredSigma s.re) *
        Real.exp (-τ * Real.log (q : ℝ)) := by
  rw [centeredSigma_cfzpHorizontalRealShift]
  unfold primeMirrorLeftAmplitude
  have harg :
      -(centeredSigma s.re + τ) * Real.log (q : ℝ) =
        -centeredSigma s.re * Real.log (q : ℝ) +
          (-τ * Real.log (q : ℝ)) := by
    ring
  rw [harg]
  rw [Real.exp_add]

/-! ## B. Signed logarithmic nodes -/

noncomputable def cfzpPrimePowerPositiveLogNode (q : ℕ) : ℂ :=
  (Real.log (q : ℝ) : ℂ)

noncomputable def cfzpPrimePowerNegativeLogNode (q : ℕ) : ℂ :=
  -(Real.log (q : ℝ) : ℂ)

theorem cfzpPrimePowerNegativeLogNode_eq_neg_positiveLogNode (q : ℕ) :
    cfzpPrimePowerNegativeLogNode q =
      -cfzpPrimePowerPositiveLogNode q := by
  rfl

theorem cfzpPrimePowerPositiveLogNode_ne_zero
    {q : ℕ} (hq : 1 < q) :
    cfzpPrimePowerPositiveLogNode q ≠ 0 := by
  unfold cfzpPrimePowerPositiveLogNode
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast hq)))

theorem cfzpPrimePowerNegativeLogNode_ne_zero
    {q : ℕ} (hq : 1 < q) :
    cfzpPrimePowerNegativeLogNode q ≠ 0 := by
  rw [cfzpPrimePowerNegativeLogNode_eq_neg_positiveLogNode]
  exact neg_ne_zero.mpr (cfzpPrimePowerPositiveLogNode_ne_zero hq)

@[simp] theorem conj_cfzpPrimePowerPositiveLogNode (q : ℕ) :
    conj (cfzpPrimePowerPositiveLogNode q) =
      cfzpPrimePowerPositiveLogNode q := by
  simp only [cfzpPrimePowerPositiveLogNode, Complex.conj_ofReal]

@[simp] theorem conj_cfzpPrimePowerNegativeLogNode (q : ℕ) :
    conj (cfzpPrimePowerNegativeLogNode q) =
      cfzpPrimePowerNegativeLogNode q := by
  simp only [cfzpPrimePowerNegativeLogNode, map_neg,
    Complex.conj_ofReal]

theorem cfzpPrimePowerPositiveLogNode_ne_negativeLogNode
    {q : ℕ} (hq : 1 < q) :
    cfzpPrimePowerPositiveLogNode q ≠
      cfzpPrimePowerNegativeLogNode q := by
  intro h
  have hre := congrArg Complex.re h
  change Real.log (q : ℝ) = -Real.log (q : ℝ) at hre
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  linarith

/-! ## C. Signed coefficients -/

noncomputable def cfzpPrimePowerPositiveLogCoefficient
    (q : ℕ) (s : ℂ) : ℂ :=
  ((canonicalPrimePowerShadowCost q : ℝ) : ℂ) *
    cfzpPrimePowerCommonRadialCarrier q *
      (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
        cfzpPrimePowerCycleState q (-s.im) /
          cfzpPrimePowerPositiveLogNode q

noncomputable def cfzpPrimePowerNegativeLogCoefficient
    (q : ℕ) (s : ℂ) : ℂ :=
  ((canonicalPrimePowerShadowCost q : ℝ) : ℂ) *
    cfzpPrimePowerCommonRadialCarrier q *
      (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
        cfzpPrimePowerCycleState q s.im /
          cfzpPrimePowerPositiveLogNode q

private theorem cfzp_exp_positiveLogNode
    (q : ℕ) (τ : ℝ) :
    Complex.exp ((τ : ℂ) * cfzpPrimePowerPositiveLogNode q) =
      (Real.exp (τ * Real.log (q : ℝ)) : ℂ) := by
  unfold cfzpPrimePowerPositiveLogNode
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]

private theorem cfzp_exp_negativeLogNode
    (q : ℕ) (τ : ℝ) :
    Complex.exp ((τ : ℂ) * cfzpPrimePowerNegativeLogNode q) =
      (Real.exp (-τ * Real.log (q : ℝ)) : ℂ) := by
  unfold cfzpPrimePowerNegativeLogNode
  have harg :
      (τ : ℂ) * -(Real.log (q : ℝ) : ℂ) =
        ((-τ * Real.log (q : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul]
    congr 1
    ring
  rw [harg, ← Complex.ofReal_exp]

theorem cfzpCanonicalFunctionalReflectionScaledMode_cfzpHorizontalRealShift_eq_signedLogFeature
    {q : ℕ} (hq : 1 < q) (s : ℂ) (τ : ℝ) :
    cfzpCanonicalFunctionalReflectionScaledMode q
        (cfzpHorizontalRealShift s τ) =
      cfzpPrimePowerPositiveLogCoefficient q s *
          (cfzpPrimePowerPositiveLogNode q *
            Complex.exp ((τ : ℂ) * cfzpPrimePowerPositiveLogNode q)) +
        cfzpPrimePowerNegativeLogCoefficient q s *
          (cfzpPrimePowerNegativeLogNode q *
            Complex.exp ((τ : ℂ) * cfzpPrimePowerNegativeLogNode q)) := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hlogne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogpos
  have hlogneC : (Real.log (q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hlogne
  have hfactor :=
    cfzpFunctionalReflectionModeDifference_eq_commonRadial_mul_phaseDisplacedAmplitude
      hqpos (cfzpHorizontalRealShift s τ)
  rw [cfzpHorizontalRealShift_im] at hfactor
  rw [primeMirrorRightAmplitude_cfzpHorizontalRealShift,
    primeMirrorLeftAmplitude_cfzpHorizontalRealShift] at hfactor
  simp only [Complex.ofReal_mul] at hfactor
  unfold cfzpCanonicalFunctionalReflectionScaledMode
    cfzpPrimePowerPositiveLogCoefficient
    cfzpPrimePowerNegativeLogCoefficient
  rw [hfactor, cfzp_exp_positiveLogNode, cfzp_exp_negativeLogNode]
  unfold cfzpPrimePowerPositiveLogNode
    cfzpPrimePowerNegativeLogNode
  field_simp [hlogneC]
  ring

theorem cfzpCanonicalFunctionalReflectionScaledMode_eq_signedLogNodeLinearCombination
    {q : ℕ} (hq : 1 < q) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionScaledMode q s =
      cfzpPrimePowerPositiveLogCoefficient q s *
          cfzpPrimePowerPositiveLogNode q +
        cfzpPrimePowerNegativeLogCoefficient q s *
          cfzpPrimePowerNegativeLogNode q := by
  simpa [cfzpHorizontalRealShift] using
    (cfzpCanonicalFunctionalReflectionScaledMode_cfzpHorizontalRealShift_eq_signedLogFeature
      hq s 0)

/-! ## D. A `Fin 2` signed feature package -/

noncomputable def cfzpPrimePowerSignedLogNodeFamily
    (q : ℕ) : Fin 2 → ℂ :=
  ![cfzpPrimePowerPositiveLogNode q, cfzpPrimePowerNegativeLogNode q]

noncomputable def cfzpPrimePowerSignedLogCoefficientFamily
    (q : ℕ) (s : ℂ) : Fin 2 → ℂ :=
  ![cfzpPrimePowerPositiveLogCoefficient q s,
    cfzpPrimePowerNegativeLogCoefficient q s]

theorem cfzpPrimePowerSignedLogFeatureFamily_sum_eq_scaledMode
    {q : ℕ} (hq : 1 < q) (s : ℂ) (τ : ℝ) :
    ∑ k : Fin 2,
      cfzpPrimePowerSignedLogCoefficientFamily q s k *
        (cfzpPrimePowerSignedLogNodeFamily q k *
          Complex.exp ((τ : ℂ) * cfzpPrimePowerSignedLogNodeFamily q k)) =
      cfzpCanonicalFunctionalReflectionScaledMode q
        (cfzpHorizontalRealShift s τ) := by
  simpa [cfzpPrimePowerSignedLogCoefficientFamily,
    cfzpPrimePowerSignedLogNodeFamily] using
    (cfzpCanonicalFunctionalReflectionScaledMode_cfzpHorizontalRealShift_eq_signedLogFeature
      hq s τ).symm

/-! ## E. Per-mode fixed-box Gram energy -/

noncomputable def cfzpPrimePowerSignedTwoNodeGramEnergy
    (ε : ℝ) (q : ℕ) (s : ℂ) : ℝ :=
  mellinQuadraticBoxGramEnergy ε
    (cfzpPrimePowerSignedLogNodeFamily q)
    (cfzpPrimePowerSignedLogCoefficientFamily q s)

theorem cfzpPrimePowerSignedTwoNodeGramEnergy_eq_shifted_scaledMode_integral
    {q : ℕ} (hq : 1 < q) (ε : ℝ) (s : ℂ) :
    cfzpPrimePowerSignedTwoNodeGramEnergy ε q s =
      (2 * ε)⁻¹ *
        ∫ τ in (-ε)..ε,
          Complex.normSq
            (cfzpCanonicalFunctionalReflectionScaledMode q
              (cfzpHorizontalRealShift s τ)) := by
  unfold cfzpPrimePowerSignedTwoNodeGramEnergy
    mellinQuadraticBoxGramEnergy
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with τ
  intro _
  rw [← cfzpPrimePowerSignedLogFeatureFamily_sum_eq_scaledMode hq s τ]

theorem cfzpPrimePowerSignedTwoNodeGramEnergy_nonneg
    {q : ℕ} (_hq : 1 < q) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    0 ≤ cfzpPrimePowerSignedTwoNodeGramEnergy ε q s := by
  unfold cfzpPrimePowerSignedTwoNodeGramEnergy
  exact mellinQuadraticBoxGramEnergy_nonneg hε _ _

/-! This is the deliberate stopping boundary: no finite canonical support is
enumerated as one `Fin (2 * N)` spectral family in this checkpoint. -/

inductive CfzpSignedPrimePowerFamilyToFullMellinGramBridgeGap : Prop
  | noFiniteCanonicalSignedSupportEnumerationProvided

end DkMath.RH.CFBRCProjection
