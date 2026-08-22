/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit
import Mathlib.Tactic

/-!
# GWSS-003G: actual synthesized shifted-energy audit

This module applies fixed-reference polarization to the actual finite
nonzero-`τ` `WholeBoxFeature` from GWSS-003F3.  It defines the four normalized
shifted energies, proves the finite-window integrability needed to use them,
and records their exact whole-source and finite-approximant readouts.

The identities in this file are representation and polarization identities.
They do not assert an ordering between the two energies, a source-side sign,
an asymptotic statement, or the Riemann hypothesis.  The final declarations
make the remaining dominance provider explicit.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open MeasureTheory
open scoped BigOperators Interval Topology

/-! ## A finite-window continuity adapter -/

private theorem continuousOn_intervalIntegral_mul_continuousKernel
    {a b c d : ℝ} {K : ℝ → ℝ → ℂ} {g : ℝ → ℂ}
    (hK : Continuous (Function.uncurry K))
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn
      (fun u : ℝ => ∫ t in a..b, g t * K t u)
      (Set.uIcc c d) := by
  have hgOn : IntegrableOn g (Set.uIoc a b) volume :=
    intervalIntegrable_iff.mp hg
  have hcompact : IsCompact (Set.uIcc a b ×ˢ Set.uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ :=
    hcompact.exists_bound_of_continuousOn hK.continuousOn
  intro u hu
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (x₀ := u) (s := Set.uIcc c d)
  · exact Filter.Eventually.of_forall (fun v => by
      have hKv : ContinuousOn (fun t : ℝ => K t v) (Set.uIcc a b) := by
        exact (hK.comp (continuous_id.prodMk continuous_const)).continuousOn
      have hmul : IntegrableOn
          (fun t : ℝ => K t v * g t) (Set.uIoc a b) volume :=
        IntegrableOn.continuousOn_mul_of_subset hKv hgOn isCompact_uIcc
          measurableSet_uIoc Set.uIoc_subset_uIcc
      simpa only [mul_comm] using hmul.1)
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact Filter.Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      have htv : (t, v) ∈ Set.uIcc a b ×ˢ Set.uIcc c d := ⟨ht', hv⟩
      calc
        ‖g t * K t v‖ = ‖(Function.uncurry K) (t, v)‖ * ‖g t‖ := by
          rw [norm_mul]
          simp only [Function.uncurry_apply_pair]
          ring
        _ ≤ C * ‖g t‖ := by
          gcongr
          exact hC (t, v) htv)
  · exact hg.norm.const_mul C
  · exact Filter.Eventually.of_forall (fun t ht => by
      have hKt : Continuous (fun v : ℝ => K t v) := by
        exact hK.comp (continuous_const.prodMk continuous_id)
      exact (continuous_const.mul hKt).continuousWithinAt)

/-! ## GWSS-003G-1: actual shifted energies -/

section ActualFeature

variable {n : ℕ}

/-- The normalized `+1` shifted energy of the actual synthesized whole
feature.  The normalization is the same `(2 * ε)⁻¹` normalization used by the
GWSS-003F3 whole-source representation. -/
noncomputable def pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + 1)

/-- The normalized `-1` shifted energy of the actual synthesized whole
feature. -/
noncomputable def pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy
    (ε : ℝ) (τ : Fin n → ℝ)
    (c : Fin n → ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - 1)

/-- The normalized `+I` shifted energy of the actual synthesized whole
feature.  This is the second real-reference polarization channel. -/
noncomputable def pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy
    (ε : ℝ) (τ : Fin n → ℝ)
    (c : Fin n → ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + Complex.I)

/-- The normalized `-I` shifted energy of the actual synthesized whole
feature. -/
noncomputable def pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy
    (ε : ℝ) (τ : Fin n → ℝ)
    (c : Fin n → ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ((2 * ε)⁻¹) *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - Complex.I)

/-! ## GWSS-003G-2: interval-integrability -/

private theorem wholeFeature_intervalIntegrable
    {ε : ℝ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X)
      volume (-ε) ε := by
  have hV :=
    pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature_intervalIntegrable
      ε τ c W X
  have hT :=
    pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature_intervalIntegrable
      ε τ c W
  change IntervalIntegrable
    (fun u : ℝ =>
      pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature τ c W X u -
        Complex.I * pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ c W u)
    volume (-ε) ε
  exact hV.sub (hT.const_mul Complex.I)

private theorem wholeFeature_continuousOn
    {ε : ℝ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ContinuousOn
      (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X)
      (Set.uIcc (-ε) ε) := by
  let Kv : ℝ → ℝ → ℂ := fun t u =>
    ∑ i, c i * pascalCenteredXiMellinGeneralTauVerticalBoxKernel (τ i) W t u
  have hKv : Continuous (Function.uncurry Kv) := by
    dsimp [Kv]
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul
      (continuous_pascalCenteredXiMellinGeneralTauVerticalBoxKernel (τ i) W)
  let Kt : ℝ → ℝ → ℂ := fun x v =>
    ∑ i, c i * pascalCenteredXiMellinGeneralTauTopBoxKernel (τ i) W x v
  have hKt : Continuous (Function.uncurry Kt) := by
    dsimp [Kt]
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul
      (continuous_pascalCenteredXiMellinGeneralTauTopBoxKernel (τ i) W)
  have hV := continuousOn_intervalIntegral_mul_continuousKernel
    (a := -W.rectangle.T) (b := W.rectangle.T)
    (c := -ε) (d := ε)
    (K := Kv)
    (g := pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X)
    hKv
    (pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable W X)
  have hT := continuousOn_intervalIntegral_mul_continuousKernel
    (a := W.rectangle.σ) (b := 1 - W.rectangle.σ)
    (c := -ε) (d := ε)
    (K := Kt)
    (g := pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W)
    hKt
    (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_intervalIntegrable W)
  have hVeq : (fun u : ℝ =>
      pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature τ c W X u) =
      (fun u : ℝ =>
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t * Kv t u) := by
    funext u
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t ht
    simp only [Kv, pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature,
      pascalCenteredXiMellinGeneralTauVerticalBoxFeature,
      pascalCenteredXiMellinGeneralTauVerticalBoxKernel]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hTeq : (fun u : ℝ =>
      pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ c W u) =
      (fun u : ℝ =>
        ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
          pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x * Kt x u) := by
    funext u
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x hx
    simp only [Kt, pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature,
      pascalCenteredXiMellinGeneralTauTopBoxFeature,
      pascalCenteredXiMellinGeneralTauTopBoxKernel]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change ContinuousOn
    (fun u : ℝ =>
      pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature τ c W X u -
        Complex.I * pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ c W u)
    (Set.uIcc (-ε) ε)
  have hcont : ContinuousOn
      (fun u : ℝ =>
        (∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t * Kv t u) -
        Complex.I *
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x * Kt x u)
      (Set.uIcc (-ε) ε) := by
    exact hV.sub ((continuousOn_const : ContinuousOn
      (fun _ : ℝ => (Complex.I : ℂ)) (Set.uIcc (-ε) ε)).mul hT)
  have hfun :
      (fun u : ℝ =>
        pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature τ c W X u -
          Complex.I * pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature τ c W u) =
      (fun u : ℝ =>
        (∫ t in (-W.rectangle.T)..W.rectangle.T,
          pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t * Kv t u) -
        Complex.I *
          ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
            pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x * Kt x u) := by
    funext u
    rw [congrFun hVeq u, congrFun hTeq u]
  rw [hfun]
  exact hcont

private theorem wholeFeature_shifted_normSq_intervalIntegrable
    {ε : ℝ} (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (r : ℂ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + r))
      volume (-ε) ε := by
  have hwhole := wholeFeature_continuousOn (ε := ε) τ c W X
  have hshift : ContinuousOn
      (fun u : ℝ =>
        pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + r)
      (Set.uIcc (-ε) ε) := hwhole.add continuousOn_const
  exact (Complex.continuous_normSq.continuousOn.comp hshift
    (fun _ _ => Set.mem_univ _)).intervalIntegrable

theorem pascalCenteredXiMellinWitnessWholeShiftedPlus_intervalIntegrable
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + 1))
      volume (-ε) ε := by
  exact wholeFeature_shifted_normSq_intervalIntegrable (ε := ε) τ c W X 1

theorem pascalCenteredXiMellinWitnessWholeShiftedMinus_intervalIntegrable
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - 1))
      volume (-ε) ε := by
  exact wholeFeature_shifted_normSq_intervalIntegrable (ε := ε) τ c W X (-1)

theorem pascalCenteredXiMellinWitnessWholeShiftedIPlus_intervalIntegrable
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + Complex.I))
      volume (-ε) ε := by
  exact wholeFeature_shifted_normSq_intervalIntegrable (ε := ε) τ c W X Complex.I

theorem pascalCenteredXiMellinWitnessWholeShiftedIMinus_intervalIntegrable
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - Complex.I))
      volume (-ε) ε := by
  exact wholeFeature_shifted_normSq_intervalIntegrable (ε := ε) τ c W X (-Complex.I)

/-! ## GWSS-003G-3: integrated polarization -/

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_normalizedIntegral_re
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c W X -
        pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c W X =
      4 *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re := by
  have hplus := pascalCenteredXiMellinWitnessWholeShiftedPlus_intervalIntegrable
    ε τ c W X
  have hminus := pascalCenteredXiMellinWitnessWholeShiftedMinus_intervalIntegrable
    ε τ c W X
  have hwhole := wholeFeature_intervalIntegrable (ε := ε) τ c W X
  have hpol :
      (fun u : ℝ =>
        Complex.normSq
            (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + 1) -
          Complex.normSq
            (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - 1)) =
      (fun u : ℝ =>
        4 * (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re) := by
    funext u
    have h := normSq_shifted_difference_one_eq_four_mul_re
      (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u)
    simpa using congrArg Complex.re h
  unfold pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy
    pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy
  rw [← mul_sub, ← intervalIntegral.integral_sub hplus hminus]
  rw [show
      (∫ u in (-ε)..ε,
          (Complex.normSq
              (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + 1) -
            Complex.normSq
              (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - 1))) =
        ∫ u in (-ε)..ε,
          4 * (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with u hu
          exact congrFun hpol u]
  rw [intervalIntegral.integral_const_mul]
  have hnorm_re :
      (((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re =
        (2 * ε)⁻¹ *
          (∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re := by
    simp [Complex.mul_re]
  have hre :
      (∫ u in (-ε)..ε,
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re) =
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).re := by
    exact intervalIntegral.intervalIntegral_re hwhole
  rw [hnorm_re, ← hre]
  ring

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_neg_four_mul_normalizedIntegral_im
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ c W X -
        pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ c W X =
      4 *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          ∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im := by
  have hplus := pascalCenteredXiMellinWitnessWholeShiftedIPlus_intervalIntegrable
    ε τ c W X
  have hminus := pascalCenteredXiMellinWitnessWholeShiftedIMinus_intervalIntegrable
    ε τ c W X
  have hwhole := wholeFeature_intervalIntegrable (ε := ε) τ c W X
  have hpol :
      (fun u : ℝ =>
        Complex.normSq
            (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + Complex.I) -
          Complex.normSq
            (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - Complex.I)) =
      (fun u : ℝ =>
        4 * (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im) := by
    funext u
    have h := normSq_shifted_difference_I_eq_four_mul_im
      (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u)
    simpa using congrArg Complex.re h
  unfold pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy
    pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy
  rw [← mul_sub, ← intervalIntegral.integral_sub hplus hminus]
  rw [show
      (∫ u in (-ε)..ε,
          (Complex.normSq
              (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + Complex.I) -
            Complex.normSq
              (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u - Complex.I))) =
        ∫ u in (-ε)..ε,
          4 * (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with u hu
          exact congrFun hpol u]
  rw [intervalIntegral.integral_const_mul]
  have hnorm_im :
      (((2 * ε : ℝ)⁻¹ : ℂ) *
        ∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im =
        (2 * ε)⁻¹ *
          (∫ u in (-ε)..ε,
            pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im := by
    simp [Complex.mul_im]
  have him :
      (∫ u in (-ε)..ε,
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im) =
        (∫ u in (-ε)..ε,
          pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u).im := by
    exact intervalIntegral.intervalIntegral_im hwhole
  rw [hnorm_im, ← him]
  ring

/-! ## GWSS-003G-4--5: exact source and finite readouts -/

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c W X -
        pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c W X =
      4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).re := by
  rw [pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_normalizedIntegral_re]
  rw [← pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
    hε τ c hτ W X]

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ c W X -
        pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ c W X =
      4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).im := by
  rw [pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_neg_four_mul_normalizedIntegral_im]
  rw [← pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
    hε τ c hτ W X]

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_two_mul_finiteApproximant_im
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c W X -
        pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c W X =
      2 * (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X).im := by
  calc
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).re :=
      pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
        hε τ c hτ W X
    _ = 2 * (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X).im := by
      rw [pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
        hε τ c W X]
      norm_num [Complex.mul_im, Complex.mul_re]
      ring

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_neg_two_mul_finiteApproximant_re
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ c W X -
        pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ c W X =
      -2 * (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X).re := by
  calc
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).im :=
      pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
        hε τ c hτ W X
    _ = -2 * (pascalCenteredXiFiniteArithmeticApproximant
        (pascalCenteredXiMellinWitnessWeight ε τ c) W X).re := by
      rw [pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
        hε τ c W X]
      norm_num [Complex.mul_im, Complex.mul_re]
      ring

/-! ## GWSS-003G-6: `q.im` transport -/

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_qIm_const_mul
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (q : ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (fun i => (q.im : ℂ) * c i) W X -
      pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (fun i => (q.im : ℂ) * c i) W X) =
      q.im *
        (pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c W X -
          pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c W X) := by
  calc
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (fun i => (q.im : ℂ) * c i) W X).re :=
      pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
        hε τ (fun i => (q.im : ℂ) * c i) hτ W X
    _ = q.im *
        (4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).re) := by
      rw [pascalCenteredXiMellinGeneralTauWitnessWholeSource_const_mul]
      norm_num [Complex.mul_re]
      ring
    _ = _ := by
      rw [← pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
        hε τ c hτ W X]

theorem pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_qIm_const_mul
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (q : ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (fun i => (q.im : ℂ) * c i) W X -
      pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (fun i => (q.im : ℂ) * c i) W X) =
      q.im *
        (pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ c W X -
          pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ c W X) := by
  calc
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (fun i => (q.im : ℂ) * c i) W X).im :=
      pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
        hε τ (fun i => (q.im : ℂ) * c i) hτ W X
    _ = q.im *
        (4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).im) := by
      rw [pascalCenteredXiMellinGeneralTauWitnessWholeSource_const_mul]
      norm_num [Complex.mul_im]
      ring
    _ = _ := by
      rw [← pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
        hε τ c hτ W X]

/-! ## GWSS-003G-7--8: the P0/P1 firewall -/

private theorem shiftedEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (r : ℂ) :
    0 ≤ ((2 * ε)⁻¹) *
      ∫ u in (-ε)..ε,
        Complex.normSq
          (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + r) := by
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass : 0 ≤ ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature τ c W X u + r) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun u => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

theorem pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c W X := by
  exact shiftedEnergy_nonneg hε τ c W X 1

theorem pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c W X := by
  exact shiftedEnergy_nonneg hε τ c W X (-1)

theorem pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ c W X := by
  exact shiftedEnergy_nonneg hε τ c W X Complex.I

theorem pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ c W X := by
  exact shiftedEnergy_nonneg hε τ c W X (-Complex.I)

/-- The `1`-reference dominance order is exactly the real-coordinate sign of
the finite whole source.  This equivalence is an audit readout, not a sign
theorem: it identifies the additional P1 provider still required. -/
theorem pascalCenteredXiMellinWitnessWholeShiftedEnergy_order_iff_wholeSource_re_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c W X ≤
        pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c W X ↔
      0 ≤ (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).re := by
  have hd := pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
    hε τ c hτ W X
  constructor <;> intro h <;> linarith

/-- The `I`-reference dominance order is exactly the imaginary-coordinate
sign of the finite whole source.  As above, the equivalence itself supplies
no independent source-side order provider. -/
theorem pascalCenteredXiMellinWitnessWholeShiftedIEnergy_order_iff_wholeSource_im_nonneg
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ)
    (hτ : ∀ i, τ i ≠ 0) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ c W X ≤
        pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ c W X ↔
      0 ≤ (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X).im := by
  have hd := pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
    hε τ c hτ W X
  constructor <;> intro h <;> linarith

end ActualFeature

end DkMath.RH.CFBRCProjection
