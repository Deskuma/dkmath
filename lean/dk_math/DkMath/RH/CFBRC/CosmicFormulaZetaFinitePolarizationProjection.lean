/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFiniteAggregateProjection
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerModeProjection
import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection"

/-!
# CFZP-004: finite polarization and same-height common carriers

This module keeps the finite amplitude polarization of CFZP-003 separate
from the signed complex PHZ mirror channel.  Each positive prime-power mode
has its own common radial/cycle carrier, so no carrier is factored out of the
finite sum.  The linear mirror difference is quadraticized mode by mode;
the resulting carrier-weighted ledger is intentionally distinct from the
raw amplitude Gap of CFZP-003.

No phase branch, Mellin weight, rectangle source, infinite product, or zeta
zero statement is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.CosmicFormula.ThreeElement
open DkMath.CosmicFormula.Rotation.CF2D

/-! ## Same-height common carrier -/

/-- The common radial/cycle carrier shared by a same-height mirror pair. -/
noncomputable def cfzpPrimePowerSameHeightCommonCarrier
    (q : ℕ) (s : ℂ) : ℂ :=
  cfzpPrimePowerCommonRadialCarrier q *
    cfzpPrimePowerCycleState q s.im

theorem cfzpPrimePowerSameHeightCommonCarrier_ne_zero
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpPrimePowerSameHeightCommonCarrier q s ≠ 0 := by
  unfold cfzpPrimePowerSameHeightCommonCarrier
  apply mul_ne_zero
  · unfold cfzpPrimePowerCommonRadialCarrier
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by exact_mod_cast hq.ne')
  · exact Complex.exp_ne_zero _

/-! ## Actual mode recovery -/

theorem natCpowNeg_eq_sameHeightCarrier_mul_leftAmplitude
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) =
      cfzpPrimePowerSameHeightCommonCarrier q s *
        (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) := by
  calc
    (q : ℂ) ^ (-s) =
        cfzpPrimePowerCommonRadialCarrier q *
          (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q s.im :=
      natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle hq s
    _ = cfzpPrimePowerSameHeightCommonCarrier q s *
          (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) := by
      unfold cfzpPrimePowerSameHeightCommonCarrier
      ring

theorem natCpowNeg_criticalMirror_eq_sameHeightCarrier_mul_rightAmplitude
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-(criticalMirror s)) =
      cfzpPrimePowerSameHeightCommonCarrier q s *
        (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) := by
  calc
    (q : ℂ) ^ (-(criticalMirror s)) =
        cfzpPrimePowerCommonRadialCarrier q *
          (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q s.im :=
      natCpowNeg_criticalMirror_eq_commonRadial_mul_rightAmplitude_mul_cycle
        hq s
    _ = cfzpPrimePowerSameHeightCommonCarrier q s *
          (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) := by
      unfold cfzpPrimePowerSameHeightCommonCarrier
      ring

/-! ## Linear same-height mirror channel -/

/-- The signed complex same-height critical-mirror mode difference. -/
noncomputable def cfzpSameHeightMirrorModeDifference
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-(criticalMirror s)) -
    (q : ℂ) ^ (-s)

theorem cfzpSameHeightMirrorModeDifference_eq_commonCarrier_mul_amplitudeDifference
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpSameHeightMirrorModeDifference q s =
      cfzpPrimePowerSameHeightCommonCarrier q s *
        (((primeMirrorRightAmplitude q (centeredSigma s.re) -
          primeMirrorLeftAmplitude q (centeredSigma s.re) : ℝ) : ℂ)) := by
  unfold cfzpSameHeightMirrorModeDifference
  rw [natCpowNeg_criticalMirror_eq_sameHeightCarrier_mul_rightAmplitude hq s,
    natCpowNeg_eq_sameHeightCarrier_mul_leftAmplitude hq s]
  simp only [Complex.ofReal_sub]
  ring

theorem normSq_cfzpSameHeightMirrorModeDifference
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    Complex.normSq (cfzpSameHeightMirrorModeDifference q s) =
      Complex.normSq (cfzpPrimePowerSameHeightCommonCarrier q s) *
        primeMirrorOffsetGap q (centeredSigma s.re) := by
  rw [cfzpSameHeightMirrorModeDifference_eq_commonCarrier_mul_amplitudeDifference
    hq s, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  unfold primeMirrorOffsetGap
  ring

/-! ## Amplitude plus/minus polarization -/

noncomputable def cfzpAggregateMirrorPlusWholeUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cf2dPlusWhole (primeMirrorOffsetState q δ)

noncomputable def cfzpAggregateMirrorMinusWholeUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cf2dMinusWhole (primeMirrorOffsetState q δ)

theorem cfzpAggregateMirrorPlusWholeUpTo_eq_big_add_body
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorPlusWholeUpTo X δ =
      cfzpAggregateMirrorBigUpTo X δ +
        cfzpAggregateMirrorBodyUpTo X δ := by
  unfold cfzpAggregateMirrorPlusWholeUpTo
    cfzpAggregateMirrorBigUpTo cfzpAggregateMirrorBodyUpTo
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [cf2dPlusWhole, squareMass, cf2dInteractionBeam,
    DkMath.CosmicFormula.ThreeElement.plusWhole,
    DkMath.CosmicFormula.ThreeElement.interactionBeam,
    DkMath.CosmicFormula.ThreeElement.coreTerm,
    DkMath.CosmicFormula.ThreeElement.gapTerm,
    pow_two]
  ring

theorem cfzpAggregateMirrorMinusWholeUpTo_eq_big_sub_body
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorMinusWholeUpTo X δ =
      cfzpAggregateMirrorBigUpTo X δ -
        cfzpAggregateMirrorBodyUpTo X δ := by
  unfold cfzpAggregateMirrorMinusWholeUpTo
    cfzpAggregateMirrorBigUpTo cfzpAggregateMirrorBodyUpTo
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [cf2dMinusWhole, squareMass, cf2dInteractionBeam,
    DkMath.CosmicFormula.ThreeElement.minusWhole,
    DkMath.CosmicFormula.ThreeElement.interactionBeam,
    DkMath.CosmicFormula.ThreeElement.coreTerm,
    DkMath.CosmicFormula.ThreeElement.gapTerm,
    pow_two]
  ring

theorem cfzpAggregateMirrorMinusWholeUpTo_eq_gap
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorMinusWholeUpTo X δ =
      cfzpAggregateMirrorGapUpTo X δ := by
  unfold cfzpAggregateMirrorMinusWholeUpTo cfzpAggregateMirrorGapUpTo
  apply Finset.sum_congr rfl
  intro q hq
  rw [primeMirrorOffsetState_minusWhole_eq_gap]

theorem cfzpAggregateMirrorPlusWholeUpTo_add_minusWholeUpTo_eq_two_mul_big
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorPlusWholeUpTo X δ +
        cfzpAggregateMirrorMinusWholeUpTo X δ =
      2 * cfzpAggregateMirrorBigUpTo X δ := by
  rw [cfzpAggregateMirrorPlusWholeUpTo_eq_big_add_body,
    cfzpAggregateMirrorMinusWholeUpTo_eq_big_sub_body]
  ring

theorem cfzpAggregateMirrorPlusWholeUpTo_sub_minusWholeUpTo_eq_two_mul_body
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorPlusWholeUpTo X δ -
        cfzpAggregateMirrorMinusWholeUpTo X δ =
      2 * cfzpAggregateMirrorBodyUpTo X δ := by
  rw [cfzpAggregateMirrorPlusWholeUpTo_eq_big_add_body,
    cfzpAggregateMirrorMinusWholeUpTo_eq_big_sub_body]
  ring

/-! ## Finite canonical PHZ mirror difference -/

noncomputable def cfzpCanonicalSameHeightMirrorLinearSourceUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q : ℂ) *
      cfzpSameHeightMirrorModeDifference q s

theorem cfzpCanonicalSameHeightMirrorLinearSourceUpTo_eq_PHZ_difference
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalSameHeightMirrorLinearSourceUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X (criticalMirror s) -
        pascalPrimePowerPHZCanonicalUpTo X s := by
  unfold cfzpCanonicalSameHeightMirrorLinearSourceUpTo
    cfzpSameHeightMirrorModeDifference
  rw [pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem cfzpCanonicalSameHeightMirrorLinearSourceUpTo_eq_commonCarrier_sum
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalSameHeightMirrorLinearSourceUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        (canonicalPrimePowerShadowCost q : ℂ) *
          (cfzpPrimePowerSameHeightCommonCarrier q s *
            (((primeMirrorRightAmplitude q (centeredSigma s.re) -
              primeMirrorLeftAmplitude q (centeredSigma s.re) : ℝ) : ℂ))) := by
  unfold cfzpCanonicalSameHeightMirrorLinearSourceUpTo
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := by
    have hqone := one_lt_of_mem_canonicalPrimePowerSupportUpTo hq
    omega
  rw [cfzpSameHeightMirrorModeDifference_eq_commonCarrier_mul_amplitudeDifference
    hqpos s]

/-! ## Carrier-weighted quadratic Gap ledger -/

noncomputable def cfzpAggregateCarrierWeightedMirrorGapUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      Complex.normSq (cfzpPrimePowerSameHeightCommonCarrier q s) *
        primeMirrorOffsetGap q (centeredSigma s.re)

theorem cfzpAggregateCarrierWeightedMirrorGapUpTo_eq_modeDifferenceNormSqSum
    (X : ℕ) (s : ℂ) :
    cfzpAggregateCarrierWeightedMirrorGapUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        canonicalPrimePowerShadowCost q *
          Complex.normSq (cfzpSameHeightMirrorModeDifference q s) := by
  unfold cfzpAggregateCarrierWeightedMirrorGapUpTo
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := by
    have hqone := one_lt_of_mem_canonicalPrimePowerSupportUpTo hq
    omega
  rw [normSq_cfzpSameHeightMirrorModeDifference hqpos s]
  ring

theorem cfzpAggregateCarrierWeightedMirrorGapUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpAggregateCarrierWeightedMirrorGapUpTo X s := by
  unfold cfzpAggregateCarrierWeightedMirrorGapUpTo
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg
    (mul_nonneg (canonicalPrimePowerShadowCost_pos_of_mem hq).le
      (Complex.normSq_nonneg _))
    (primeMirrorOffsetGap_nonneg q (centeredSigma s.re))

end DkMath.RH.CFBRCProjection
