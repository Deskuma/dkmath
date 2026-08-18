/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPositiveCarrierWeightedMassAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExactCarrierRemainderSignedMomentAudit"

/-!
# CFZP-039: exact prime-axis carrier/remainder signed moment

The eligible prime axis is kept as a finite signed sum.  CFZP-036 splits
each coordinate amplitude into a periodic carrier and a finite `K / log p`
remainder; this file lifts that identity through the exact signed ledger.
No prime-distribution, infinite-sum, or residual-elimination theorem is
introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Set

/-! ## Gate A: exact finite carrier/remainder masses -/

/-! The definitions below deliberately accept arbitrary finite pair supports;
the eligible-support hypotheses are used only by the exactness theorems. -/

/-! The sigma-weighted leading periodic carrier mass. -/
noncomputable def cfzp039PrimeAxisLeadingCarrierMassOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp034PrimeAxisSigmaWeight W pk.1 *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (Real.log (pk.1 : ℝ))

/-! The sigma-weighted finite coordinate-amplitude remainder mass. -/
noncomputable def cfzp039PrimeAxisRemainderMassOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp034PrimeAxisSigmaWeight W pk.1 *
      cfzp036PrimeAxisAmplitudeRemainder ε W
        (Real.log (pk.1 : ℝ))

private theorem cfzp039_eligible_pair_data
    {ε : ℝ}
    {A B : ℕ} (hAB : A ≤ B)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    Nat.Prime pk.1 ∧ pk.2 = 0 ∧ Cfzp034PrimeAxisMassEligible ε pk.1 := by
  classical
  have haxis := (Finset.mem_filter.mp hpk).1
  have heligible := (Finset.mem_filter.mp hpk).2
  have hblock := (Finset.mem_filter.mp haxis).1
  have hzero := (Finset.mem_filter.mp haxis).2
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hblock)
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  exact ⟨hp, hzero, heligible⟩

private theorem cfzp039_eligible_log_safe
    {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (h : Cfzp034PrimeAxisMassEligible ε p) :
    1 ≤ Real.log (p : ℝ) ∧ 2 * ε ≤ Real.log (p : ℝ) :=
  ⟨h.2, cfzp034PrimeAxisMassEligible_two_epsilon_le hε h⟩

private theorem cfzp039_eligible_coordinate_decomposition
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (h : Cfzp034PrimeAxisMassEligible ε p) :
    cfzp036PrimeAxisCoordinateAmplitude ε W (Real.log (p : ℝ)) =
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log (p : ℝ)) +
        cfzp036PrimeAxisAmplitudeRemainder ε W (Real.log (p : ℝ)) := by
  have hsafe := cfzp039_eligible_log_safe hε h
  have hu0 : 0 < Real.log (p : ℝ) := lt_of_lt_of_le (by positivity) hsafe.1
  have hl : Real.log (p : ℝ) - ε ≠ 0 := by
    have : 0 < Real.log (p : ℝ) - ε := by linarith [hsafe.2]
    exact this.ne'
  have hr : Real.log (p : ℝ) + ε ≠ 0 := by
    have : 0 < Real.log (p : ℝ) + ε := by linarith
    exact this.ne'
  exact cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder
    hε.ne' hl hr W

private theorem cfzp039_eligible_signed_mass_term_eq_carrier_add_remainder
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
        cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1) =
      cfzp034PrimeAxisSigmaWeight W pk.1 *
        (cfzp036PrimeAxisLeadingPeriodicCarrier ε W
            (Real.log (pk.1 : ℝ)) +
          cfzp036PrimeAxisAmplitudeRemainder ε W
            (Real.log (pk.1 : ℝ))) := by
  obtain ⟨hp, hzero, heligible⟩ := cfzp039_eligible_pair_data hAB hpk
  have hj : 0 < pk.2 + 1 := by omega
  have hevent := cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    hε hε2 W hp hj
  have htransport := cfzp035PrimeAxisEvent_eq_sigmaWeight_mul_signedAmplitude
    hε hε2 W hp
  have hamp := cfzp035PrimeAxisSignedAmplitude_eq_cfzp036CoordinateAmplitude_log
    hε hε2 W hp
  have hdecomp := cfzp039_eligible_coordinate_decomposition hε W heligible
  calc
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
          cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1) =
        cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1) := hevent.symm
    _ = cfzp034PrimeAxisSigmaWeight W pk.1 *
          cfzp035PrimeAxisSignedAmplitude ε W pk.1 := by
      simpa [hzero] using htransport
    _ = cfzp034PrimeAxisSigmaWeight W pk.1 *
          cfzp036PrimeAxisCoordinateAmplitude ε W (Real.log (pk.1 : ℝ)) := by
      rw [hamp]
    _ = cfzp034PrimeAxisSigmaWeight W pk.1 *
          (cfzp036PrimeAxisLeadingPeriodicCarrier ε W
              (Real.log (pk.1 : ℝ)) +
            cfzp036PrimeAxisAmplitudeRemainder ε W
              (Real.log (pk.1 : ℝ))) := by rw [hdecomp]

theorem cfzp039PrimeAxisSignedMassOn_eq_leading_add_remainder
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    cfzp035SignedEfficiencyMassOn ε W S =
      cfzp039PrimeAxisLeadingCarrierMassOn ε W S +
        cfzp039PrimeAxisRemainderMassOn ε W S := by
  classical
  unfold cfzp035SignedEfficiencyMassOn
    cfzp039PrimeAxisLeadingCarrierMassOn
    cfzp039PrimeAxisRemainderMassOn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pk hpk
  simpa [mul_add] using cfzp039_eligible_signed_mass_term_eq_carrier_add_remainder
    hε hε2 W hAB (hS hpk)

theorem cfzp039EligiblePrimeAxisSignedMass_eq_leading_add_remainder
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp035SignedEfficiencyMassOn ε W
        (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) =
      cfzp039PrimeAxisLeadingCarrierMassOn ε W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) +
        cfzp039PrimeAxisRemainderMassOn ε W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) := by
  exact cfzp039PrimeAxisSignedMassOn_eq_leading_add_remainder
    hε hε2 W hAB _ (by intro pk hpk; exact hpk)

/-! ## Gate B: finite `K / log p` remainder debt -/

/-! The explicit finite debt envelope for the remainder mass. -/
noncomputable def cfzp039PrimeAxisRemainderDebtOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp034PrimeAxisSigmaWeight W pk.1 *
      (cfzp036PrimeAxisRemainderConstant ε W /
        Real.log (pk.1 : ℝ))

private theorem cfzp039_remainder_term_abs_le_debt_term
    {ε : ℝ} (hε : 0 < ε) (_hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    |cfzp034PrimeAxisSigmaWeight W pk.1 *
        cfzp036PrimeAxisAmplitudeRemainder ε W
          (Real.log (pk.1 : ℝ))| ≤
      cfzp034PrimeAxisSigmaWeight W pk.1 *
        (cfzp036PrimeAxisRemainderConstant ε W /
          Real.log (pk.1 : ℝ)) := by
  obtain ⟨hp, _hzero, heligible⟩ := cfzp039_eligible_pair_data hAB hpk
  have hsafe := cfzp039_eligible_log_safe hε heligible
  have hrem := cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div
    hε hsafe.1 hsafe.2 W
  rw [abs_mul, abs_of_pos (cfzp034PrimeAxisSigmaWeight_pos W pk.1)]
  exact mul_le_mul_of_nonneg_left hrem
    (cfzp034PrimeAxisSigmaWeight_pos W pk.1).le

theorem cfzp039PrimeAxisRemainderDebtOn_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    0 ≤ cfzp039PrimeAxisRemainderDebtOn ε W S := by
  classical
  unfold cfzp039PrimeAxisRemainderDebtOn
  apply Finset.sum_nonneg
  intro pk hpk
  have heligible := (hS hpk)
  have haxis := (cfzp039_eligible_pair_data hAB heligible).1
  have hlog : 0 < Real.log (pk.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast haxis.one_lt)
  exact mul_nonneg (cfzp034PrimeAxisSigmaWeight_pos W pk.1).le
    (div_nonneg (cfzp036PrimeAxisRemainderConstant_pos hε W).le hlog.le)

theorem cfzp039PrimeAxisRemainderMassOn_abs_le_debt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    |cfzp039PrimeAxisRemainderMassOn ε W S| ≤
      cfzp039PrimeAxisRemainderDebtOn ε W S := by
  classical
  unfold cfzp039PrimeAxisRemainderMassOn
    cfzp039PrimeAxisRemainderDebtOn
  calc
    |∑ pk ∈ S,
        cfzp034PrimeAxisSigmaWeight W pk.1 *
          cfzp036PrimeAxisAmplitudeRemainder ε W
            (Real.log (pk.1 : ℝ))| ≤
        ∑ pk ∈ S,
          |cfzp034PrimeAxisSigmaWeight W pk.1 *
            cfzp036PrimeAxisAmplitudeRemainder ε W
              (Real.log (pk.1 : ℝ))| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pk ∈ S,
        cfzp034PrimeAxisSigmaWeight W pk.1 *
          (cfzp036PrimeAxisRemainderConstant ε W /
            Real.log (pk.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro pk hpk
      exact cfzp039_remainder_term_abs_le_debt_term hε hε2 W hAB (hS hpk)

theorem cfzp039PrimeAxisRemainderMassOn_ge_neg_debt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    -cfzp039PrimeAxisRemainderDebtOn ε W S ≤
      cfzp039PrimeAxisRemainderMassOn ε W S := by
  have habs := cfzp039PrimeAxisRemainderMassOn_abs_le_debt
    hε hε2 W hAB S hS
  exact (neg_le_neg habs).trans
    (neg_abs_le (cfzp039PrimeAxisRemainderMassOn ε W S))

/-! ## Gate C: exact leading-carrier reservoir -/

theorem cfzp039LeadingCarrierReservoir_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp039PrimeAxisRemainderDebtOn ε W
            (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B ≤
        cfzp039PrimeAxisLeadingCarrierMassOn ε W
            (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  have hsplit := cfzp035SignedEfficiencyBlock_eq_three_way_split ε W hAB
  have hcarrier := cfzp039EligiblePrimeAxisSignedMass_eq_leading_add_remainder
    hε hε2 W hAB
  have hrem := cfzp039PrimeAxisRemainderMassOn_ge_neg_debt
    hε hε2 W hAB
      (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) (by intro pk hpk; exact hpk)
  have hex := cfzp038ExceptionalSignedMass_ge_neg_referenceMass
    hε hε2 W hAB
  have hhigher := cfzp038HigherPowerSignedMass_ge_neg_referenceMass
    hε hε2 W hAB
  apply cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le
    hε hε2 W hAB
  rw [hsplit, hcarrier]
  linarith

/-! ## Gate D: explicit interior-strip growth exponent -/

/-- The exponent left after combining prime density with sigma decay. -/
noncomputable def cfzp039PrimeAxisGrowthExponent
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  1 - W.rectangle.σ

/-- An explicit, caller-supplied interior strip for the prime-axis route. -/
def Cfzp039PrimeAxisInteriorStrip
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  W.rectangle.σ < 1

theorem cfzp039PrimeAxisGrowthExponent_pos
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    0 < cfzp039PrimeAxisGrowthExponent W := by
  unfold Cfzp039PrimeAxisInteriorStrip cfzp039PrimeAxisGrowthExponent at *
  linarith

theorem cfzp039PrimeAxisGrowthExponent_lt_half
    (W : PascalCenteredXiResidueTransportWindow)
    (_hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    cfzp039PrimeAxisGrowthExponent W < 1 / 2 := by
  unfold Cfzp039PrimeAxisInteriorStrip cfzp039PrimeAxisGrowthExponent at *
  linarith [cfzp034_rectangleSigma_gt_half W]

theorem cfzp039PrimeAxisExponentialPeriod_factor_pos
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    0 < Real.exp
        (cfzp039PrimeAxisGrowthExponent W *
          cfzp036PrimeAxisCarrierPeriod W) - 1 := by
  apply sub_pos.mpr
  have harg := mul_pos (cfzp039PrimeAxisGrowthExponent_pos W hstrip)
    (cfzp036PrimeAxisCarrierPeriod_pos W)
  have hexp := Real.add_one_le_exp
    (cfzp039PrimeAxisGrowthExponent W * cfzp036PrimeAxisCarrierPeriod W)
  linarith

/-! ## Gate E: exponential one-period coefficients -/

/-- The sine coefficient after exponential one-period transport. -/
noncomputable def cfzp039ExponentialCarrierSinCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzp039PrimeAxisGrowthExponent W *
      cfzp036LeadingSinCoeffNumerator ε W +
    W.rectangle.T * cfzp036LeadingCosCoeffNumerator ε W

/-- The cosine coefficient after exponential one-period transport. -/
noncomputable def cfzp039ExponentialCarrierCosCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzp039PrimeAxisGrowthExponent W *
      cfzp036LeadingCosCoeffNumerator ε W -
    W.rectangle.T * cfzp036LeadingSinCoeffNumerator ε W

theorem cfzp039ExponentialCarrierSinCoeff_identity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    cfzp039PrimeAxisGrowthExponent W *
          cfzp039ExponentialCarrierSinCoeff ε W -
        W.rectangle.T * cfzp039ExponentialCarrierCosCoeff ε W =
      (cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2) *
        cfzp036LeadingSinCoeffNumerator ε W := by
  unfold cfzp039ExponentialCarrierSinCoeff
    cfzp039ExponentialCarrierCosCoeff
  ring

theorem cfzp039ExponentialCarrierCosCoeff_identity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    W.rectangle.T * cfzp039ExponentialCarrierSinCoeff ε W +
          cfzp039PrimeAxisGrowthExponent W *
            cfzp039ExponentialCarrierCosCoeff ε W =
      (cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2) *
        cfzp036LeadingCosCoeffNumerator ε W := by
  unfold cfzp039ExponentialCarrierSinCoeff
    cfzp039ExponentialCarrierCosCoeff
  ring

theorem cfzp039ExponentialCarrierCoeff_pair_ne_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp039ExponentialCarrierSinCoeff ε W ≠ 0 ∨
      cfzp039ExponentialCarrierCosCoeff ε W ≠ 0 := by
  by_contra h
  push Not at h
  have hfactor : 0 <
      cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2 := by
    exact add_pos_of_nonneg_of_pos
      (sq_nonneg (cfzp039PrimeAxisGrowthExponent W))
      (sq_pos_of_pos W.rectangle.hT)
  have hsinId := cfzp039ExponentialCarrierSinCoeff_identity ε W
  have hcosId := cfzp039ExponentialCarrierCosCoeff_identity ε W
  have hsin : cfzp036LeadingSinCoeffNumerator ε W = 0 := by
    simp only [h.1, h.2, mul_zero, sub_zero] at hsinId
    nlinarith
  have hcos : cfzp036LeadingCosCoeffNumerator ε W = 0 := by
    simp only [h.1, h.2, mul_zero, add_zero] at hcosId
    nlinarith
  rcases cfzp036LeadingCoeff_pair_ne_zero hε W with hsin' | hcos'
  · exact hsin' hsin
  · exact hcos' hcos

/-! ## Gate F: the finite exponential transform model -/

/-- The positive scale of the exponential one-period transform model. -/
noncomputable def cfzp039ExponentialCarrierPeriodScale
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (Real.exp
      (cfzp039PrimeAxisGrowthExponent W *
        cfzp036PrimeAxisCarrierPeriod W) - 1) /
    (ε *
      (cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2))

theorem cfzp039ExponentialCarrierPeriodScale_pos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    0 < cfzp039ExponentialCarrierPeriodScale ε W := by
  unfold cfzp039ExponentialCarrierPeriodScale
  apply div_pos
  · exact cfzp039PrimeAxisExponentialPeriod_factor_pos W hstrip
  · apply mul_pos hε
    nlinarith [sq_nonneg (cfzp039PrimeAxisGrowthExponent W),
      W.rectangle.hT]

/-- Closed-form model for the exponentially weighted one-period carrier. -/
noncomputable def cfzp039ExponentialCarrierPeriodTransform
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  cfzp039ExponentialCarrierPeriodScale ε W *
    (cfzp039ExponentialCarrierSinCoeff ε W *
        Real.sin (W.rectangle.T * c) +
      cfzp039ExponentialCarrierCosCoeff ε W *
        Real.cos (W.rectangle.T * c))

private theorem cfzp039_transform_period_phase
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    W.rectangle.T *
        (c + cfzp036PrimeAxisCarrierPeriod W) =
      W.rectangle.T * c + 2 * Real.pi := by
  unfold cfzp036PrimeAxisCarrierPeriod
  have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
  field_simp [hT]

private theorem cfzp039_transform_half_period_phase
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    W.rectangle.T *
        (c + cfzp036PrimeAxisCarrierPeriod W / 2) =
      W.rectangle.T * c + Real.pi := by
  unfold cfzp036PrimeAxisCarrierPeriod
  have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
  field_simp [hT]

theorem cfzp039ExponentialCarrierPeriodTransform_period
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    cfzp039ExponentialCarrierPeriodTransform ε W
        (c + cfzp036PrimeAxisCarrierPeriod W) =
      cfzp039ExponentialCarrierPeriodTransform ε W c := by
  unfold cfzp039ExponentialCarrierPeriodTransform
  rw [cfzp039_transform_period_phase]
  simp only [Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem cfzp039ExponentialCarrierPeriodTransform_half_period
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    cfzp039ExponentialCarrierPeriodTransform ε W
        (c + cfzp036PrimeAxisCarrierPeriod W / 2) =
      -cfzp039ExponentialCarrierPeriodTransform ε W c := by
  unfold cfzp039ExponentialCarrierPeriodTransform
  rw [cfzp039_transform_half_period_phase]
  rw [Real.sin_add_pi, Real.cos_add_pi]
  ring

theorem cfzp039ExponentialCarrierPeriodTransform_exists_pos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    ∃ c, 0 < cfzp039ExponentialCarrierPeriodTransform ε W c := by
  have hscale := cfzp039ExponentialCarrierPeriodScale_pos hε W hstrip
  obtain hsin | hcos := cfzp039ExponentialCarrierCoeff_pair_ne_zero hε W
  · by_cases hsin_pos : 0 < cfzp039ExponentialCarrierSinCoeff ε W
    · refine ⟨Real.pi / (2 * W.rectangle.T), ?_⟩
      unfold cfzp039ExponentialCarrierPeriodTransform
      have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
      have harg : W.rectangle.T * (Real.pi / (2 * W.rectangle.T)) =
          Real.pi / 2 := by
        field_simp [hT]
      rw [harg, Real.sin_pi_div_two, Real.cos_pi_div_two]
      simpa using mul_pos hscale hsin_pos
    · have hsin_neg : cfzp039ExponentialCarrierSinCoeff ε W < 0 :=
        lt_of_le_of_ne (le_of_not_gt hsin_pos) hsin
      refine ⟨-(Real.pi / (2 * W.rectangle.T)), ?_⟩
      unfold cfzp039ExponentialCarrierPeriodTransform
      have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
      have harg : W.rectangle.T * (-(Real.pi / (2 * W.rectangle.T))) =
          -(Real.pi / 2) := by
        field_simp [hT]
      rw [harg, Real.sin_neg, Real.sin_pi_div_two, Real.cos_neg,
        Real.cos_pi_div_two, mul_zero, add_zero]
      simpa using mul_pos hscale (neg_pos.mpr hsin_neg)
  · by_cases hcos_pos : 0 < cfzp039ExponentialCarrierCosCoeff ε W
    · refine ⟨0, ?_⟩
      unfold cfzp039ExponentialCarrierPeriodTransform
      simp only [mul_zero, Real.sin_zero, Real.cos_zero]
      simpa using mul_pos hscale hcos_pos
    · have hcos_neg : cfzp039ExponentialCarrierCosCoeff ε W < 0 :=
        lt_of_le_of_ne (le_of_not_gt hcos_pos) hcos
      refine ⟨Real.pi / W.rectangle.T, ?_⟩
      unfold cfzp039ExponentialCarrierPeriodTransform
      have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
      have harg : W.rectangle.T * (Real.pi / W.rectangle.T) = Real.pi := by
        field_simp [hT]
      rw [harg, Real.sin_pi, Real.cos_pi]
      simpa using mul_pos hscale (neg_pos.mpr hcos_neg)

theorem cfzp039ExponentialCarrierPeriodTransform_exists_neg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    ∃ c, cfzp039ExponentialCarrierPeriodTransform ε W c < 0 := by
  obtain ⟨c, hc⟩ := cfzp039ExponentialCarrierPeriodTransform_exists_pos
    hε W hstrip
  refine ⟨c + cfzp036PrimeAxisCarrierPeriod W / 2, ?_⟩
  rw [cfzp039ExponentialCarrierPeriodTransform_half_period]
  linarith

/-! ## Gate H: finite period-cell support -/

/-- Left endpoint of the `n`-th translated carrier period cell. -/
noncomputable def cfzp039CarrierCellLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  c + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W

/-- Right endpoint of the `n`-th translated carrier period cell. -/
noncomputable def cfzp039CarrierCellRight
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  c + ((n + 1 : ℕ) : ℝ) * cfzp036PrimeAxisCarrierPeriod W

/-- Eligible prime-axis pairs whose log coordinate lies in one `Ioc` cell. -/
noncomputable def cfzp039PrimeAxisCarrierCellPairSupport
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n A B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (cfzp034EligiblePrimeAxisPairBlockSupport ε A B).filter
    (fun pk =>
      cfzp039CarrierCellLeft W c n < Real.log (pk.1 : ℝ) ∧
        Real.log (pk.1 : ℝ) ≤ cfzp039CarrierCellRight W c n)

theorem cfzp039PrimeAxisCarrierCellPairSupport_subset_eligible
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {c : ℝ} {n A B : ℕ} :
    cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B ⊆
      cfzp034EligiblePrimeAxisPairBlockSupport ε A B := by
  classical
  intro pk hpk
  exact (Finset.mem_filter.mp hpk).1

/-- Leading carrier mass restricted to one finite period cell. -/
noncomputable def cfzp039PrimeAxisLeadingCarrierCellMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n A B : ℕ) : ℝ :=
  cfzp039PrimeAxisLeadingCarrierMassOn ε W
    (cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B)

/-- Remainder debt restricted to one finite period cell. -/
noncomputable def cfzp039PrimeAxisRemainderCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n A B : ℕ) : ℝ :=
  cfzp039PrimeAxisRemainderDebtOn ε W
    (cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B)

theorem cfzp039PrimeAxisCarrierCellSignedMass_eq_leading_add_remainder
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {c : ℝ} {n A B : ℕ} (hAB : A ≤ B) :
    cfzp035SignedEfficiencyMassOn ε W
        (cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B) =
      cfzp039PrimeAxisLeadingCarrierCellMass ε W c n A B +
        cfzp039PrimeAxisRemainderMassOn ε W
          (cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B) := by
  exact cfzp039PrimeAxisSignedMassOn_eq_leading_add_remainder
    hε hε2 W hAB _
      (cfzp039PrimeAxisCarrierCellPairSupport_subset_eligible W)

theorem cfzp039PrimeAxisCarrierCellRemainderMass_ge_neg_debt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {c : ℝ} {n A B : ℕ} (hAB : A ≤ B) :
    -cfzp039PrimeAxisRemainderCellDebt ε W c n A B ≤
      cfzp039PrimeAxisRemainderMassOn ε W
        (cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B) := by
  exact cfzp039PrimeAxisRemainderMassOn_ge_neg_debt hε hε2 W hAB _
    (cfzp039PrimeAxisCarrierCellPairSupport_subset_eligible W)

/-! ## Firewall -/

inductive Cfzp039PrimeAxisExactCarrierRemainderSignedMomentGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noPrimeAxisCarrierCellDistributionProvider
  | noPrimeAxisCarrierAsymptoticProvider
  | noIntervalIntegralIdentification
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination

end DkMath.RH.CFBRCProjection
