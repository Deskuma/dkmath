/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaExactSignedEfficiencyNormalizationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSigmaStrippedPeriodicCarrierAudit"

/-!
# CFZP-036: prime-axis sigma-stripped periodic carrier

This module separates the finite prime-axis event into its sigma weight and a
coordinate-level oscillatory amplitude.  The amplitude is written as one
periodic sine/cosine carrier plus a finite rational remainder.  All statements
are finite identities or finite envelopes; no prime-distribution or limit
claim is made.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory

/-! ## Gate A: coordinate-level sigma stripping -/

/-- The prime-axis event after the factor `exp (-σ log p)` is removed. -/
noncomputable def cfzp036PrimeAxisCoordinateAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (u / ε) *
    (Real.exp ((cfzpModePhaseAbscissa W) * ε) /
        (u - ε) ^ 2 *
        cfzpNegativeFrequencyBoundaryCore
          (cfzpModePhaseAbscissa W) (u - ε) W.rectangle.T -
     Real.exp (-(cfzpModePhaseAbscissa W) * ε) /
        (u + ε) ^ 2 *
        cfzpNegativeFrequencyBoundaryCore
          (cfzpModePhaseAbscissa W) (u + ε) W.rectangle.T)

/-- Prime-axis specialization of the sigma-stripped coordinate amplitude. -/
theorem cfzp035PrimeAxisSignedAmplitude_eq_cfzp036CoordinateAmplitude_log
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (hp : Nat.Prime p) :
    cfzp035PrimeAxisSignedAmplitude ε W p =
      cfzp036PrimeAxisCoordinateAmplitude ε W (Real.log (p : ℝ)) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp (by norm_num : 0 < (1 : ℕ))
  have hσ : 0 < cfzp034PrimeAxisSigmaWeight W p :=
    cfzp034PrimeAxisSigmaWeight_pos W p
  have hevent := cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp (by norm_num : 0 < (1 : ℕ))
  have htransport := cfzp035PrimeAxisEvent_eq_sigmaWeight_mul_signedAmplitude
    hε hε2 W hp
  have hcoord :
      cfzpPrimePowerBranchFreeTrigEvent ε W p 1 =
        cfzp034PrimeAxisSigmaWeight W p *
          cfzp036PrimeAxisCoordinateAmplitude ε W (Real.log (p : ℝ)) := by
    rw [hevent]
    unfold cfzpPrimePowerEventPositiveScale
      cfzpNegativeFrequencyBoundaryProfile
      cfzpPrimePowerPhaseMagnitudeLeft
      cfzpPrimePowerPhaseMagnitudeRight
      cfzpPrimePowerPhaseCenter
      cfzp036PrimeAxisCoordinateAmplitude
      cfzp034PrimeAxisSigmaWeight
    have hleft : 0 < Real.log (p : ℝ) - ε := by
      simpa [cfzpPrimePowerPhaseMagnitudeLeft, cfzpPrimePowerPhaseCenter]
        using hmag.1
    have hright : 0 < Real.log (p : ℝ) + ε := by
      simpa [cfzpPrimePowerPhaseMagnitudeRight, cfzpPrimePowerPhaseCenter]
        using hmag.2
    have hexpL :
        Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) *
            Real.exp ((cfzpModePhaseAbscissa W) * ε) =
          Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
            Real.exp (-(cfzpModePhaseAbscissa W) *
              (Real.log (p : ℝ) - ε)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold cfzpModePhaseAbscissa
      congr 1
      ring
    have hexpR :
        Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) *
            Real.exp (-(cfzpModePhaseAbscissa W) * ε) =
          Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
            Real.exp (-(cfzpModePhaseAbscissa W) *
              (Real.log (p : ℝ) + ε)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold cfzpModePhaseAbscissa
      congr 1
      ring
    unfold cfzpModeCriticalScale
    simp only [pow_one, Nat.cast_one, one_mul]
    field_simp [hε.ne', hleft.ne', hright.ne']
    have hL0 :
        Real.exp (Real.log (p : ℝ) * (-1 / 2 : ℝ)) *
            Real.exp (-(Real.log (p : ℝ) * cfzpModePhaseAbscissa W) +
              cfzpModePhaseAbscissa W * ε) =
          Real.exp (-(Real.log (p : ℝ) * W.rectangle.σ)) *
            Real.exp ((cfzpModePhaseAbscissa W) * ε) := by
      have h := hexpL.symm
      ring_nf at h ⊢
      exact h
    have hR0 :
        Real.exp (Real.log (p : ℝ) * (-1 / 2 : ℝ)) *
            Real.exp (-(Real.log (p : ℝ) * cfzpModePhaseAbscissa W) -
              cfzpModePhaseAbscissa W * ε) =
          Real.exp (-(Real.log (p : ℝ) * W.rectangle.σ)) *
            Real.exp (-(cfzpModePhaseAbscissa W) * ε) := by
      have h := hexpR.symm
      ring_nf at h ⊢
      exact h
    apply sub_eq_zero.mp
    calc
      _ =
          (Real.exp (Real.log (p : ℝ) * (-1 / 2 : ℝ)) *
              Real.exp (-(Real.log (p : ℝ) * cfzpModePhaseAbscissa W) +
                cfzpModePhaseAbscissa W * ε) -
            Real.exp (-(Real.log (p : ℝ) * W.rectangle.σ)) *
              Real.exp ((cfzpModePhaseAbscissa W) * ε)) *
              (Real.log (p : ℝ) *
                cfzpNegativeFrequencyBoundaryCore
                  (cfzpModePhaseAbscissa W) (Real.log (p : ℝ) - ε)
                    W.rectangle.T * (Real.log (p : ℝ) + ε) ^ 2) -
          (Real.exp (Real.log (p : ℝ) * (-1 / 2 : ℝ)) *
              Real.exp (-(Real.log (p : ℝ) * cfzpModePhaseAbscissa W) -
                cfzpModePhaseAbscissa W * ε) -
            Real.exp (-(Real.log (p : ℝ) * W.rectangle.σ)) *
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) *
              ((Real.log (p : ℝ) - ε) ^ 2 * Real.log (p : ℝ) *
                cfzpNegativeFrequencyBoundaryCore
                  (cfzpModePhaseAbscissa W) (Real.log (p : ℝ) + ε)
                    W.rectangle.T) := by ring_nf
      _ = 0 := by rw [hL0, hR0]; ring
  apply (mul_left_cancel₀ hσ.ne')
  calc
    cfzp034PrimeAxisSigmaWeight W p *
          cfzp035PrimeAxisSignedAmplitude ε W p =
        cfzpPrimePowerBranchFreeTrigEvent ε W p 1 := htransport.symm
    _ = cfzp034PrimeAxisSigmaWeight W p *
          cfzp036PrimeAxisCoordinateAmplitude ε W (Real.log (p : ℝ)) := hcoord

/-! ## Gate B: linear phase form of the boundary core -/

/-- The linear phase part of the negative-frequency boundary core. -/
noncomputable def cfzp036LinearPhaseCore (a T θ : ℝ) : ℝ :=
  a * Real.sin θ - T * Real.cos θ

/-- The boundary core is linear phase plus the unscaled sine remainder. -/
theorem cfzpNegativeFrequencyBoundaryCore_eq_linearPhaseCore_add_sin
    (a v T : ℝ) :
    cfzpNegativeFrequencyBoundaryCore a v T =
      v * cfzp036LinearPhaseCore a T (v * T) + Real.sin (v * T) := by
  unfold cfzpNegativeFrequencyBoundaryCore cfzp036LinearPhaseCore
  ring

/-- A nonnegative phase coefficient gives a simple absolute envelope. -/
theorem cfzp036LinearPhaseCore_abs_le
    {a T θ : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    |cfzp036LinearPhaseCore a T θ| ≤ a + T := by
  have hs : |Real.sin θ| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨by linarith [Real.neg_one_le_sin θ], Real.sin_le_one θ⟩
  have hc : |Real.cos θ| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨by linarith [Real.neg_one_le_cos θ], Real.cos_le_one θ⟩
  unfold cfzp036LinearPhaseCore
  calc
    |a * Real.sin θ - T * Real.cos θ| ≤
        |a * Real.sin θ| + |T * Real.cos θ| := by
          exact abs_sub _ _
    _ = a * |Real.sin θ| + T * |Real.cos θ| := by
      rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hT]
    _ ≤ a + T := by
      simpa using add_le_add
        (mul_le_mul_of_nonneg_left hs ha)
        (mul_le_mul_of_nonneg_left hc hT)

/-! ## Gate C: exact periodic carrier and finite remainder -/

/-- The leading periodic carrier before its sine/cosine normal form. -/
noncomputable def cfzp036PrimeAxisLeadingPeriodicCarrier
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (Real.exp ((cfzpModePhaseAbscissa W) * ε) *
      cfzp036LinearPhaseCore (cfzpModePhaseAbscissa W) W.rectangle.T
        (W.rectangle.T * (u - ε)) -
    Real.exp (-(cfzpModePhaseAbscissa W) * ε) *
      cfzp036LinearPhaseCore (cfzpModePhaseAbscissa W) W.rectangle.T
        (W.rectangle.T * (u + ε))) / ε

/-- The finite rational remainder left after extracting the periodic carrier. -/
noncomputable def cfzp036PrimeAxisAmplitudeRemainder
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Real.exp ((cfzpModePhaseAbscissa W) * ε) /
      (u - ε) *
        cfzp036LinearPhaseCore (cfzpModePhaseAbscissa W) W.rectangle.T
          (W.rectangle.T * (u - ε)) +
    Real.exp (-(cfzpModePhaseAbscissa W) * ε) /
      (u + ε) *
        cfzp036LinearPhaseCore (cfzpModePhaseAbscissa W) W.rectangle.T
          (W.rectangle.T * (u + ε)) +
    (u / ε) *
      (Real.exp ((cfzpModePhaseAbscissa W) * ε) /
          (u - ε) ^ 2 * Real.sin (W.rectangle.T * (u - ε)) -
       Real.exp (-(cfzpModePhaseAbscissa W) * ε) /
          (u + ε) ^ 2 * Real.sin (W.rectangle.T * (u + ε)))

/-- Exact carrier/remainder decomposition of the coordinate amplitude. -/
theorem cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder
    {ε u : ℝ} (hε : ε ≠ 0) (hl : u - ε ≠ 0) (hr : u + ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp036PrimeAxisCoordinateAmplitude ε W u =
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u +
        cfzp036PrimeAxisAmplitudeRemainder ε W u := by
  unfold cfzp036PrimeAxisCoordinateAmplitude
    cfzp036PrimeAxisLeadingPeriodicCarrier
    cfzp036PrimeAxisAmplitudeRemainder
  rw [cfzpNegativeFrequencyBoundaryCore_eq_linearPhaseCore_add_sin]
  rw [cfzpNegativeFrequencyBoundaryCore_eq_linearPhaseCore_add_sin]
  field_simp [hε, hl, hr]
  ring

/-! ## Gate E: one sine/cosine pair -/

/-- The unnormalized sine coefficient of the periodic carrier. -/
noncomputable def cfzp036LeadingSinCoeffNumerator
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpModePhaseAbscissa W * Real.cos (W.rectangle.T * ε) *
      (Real.exp (cfzpModePhaseAbscissa W * ε) -
        Real.exp (-(cfzpModePhaseAbscissa W) * ε)) -
    W.rectangle.T * Real.sin (W.rectangle.T * ε) *
      (Real.exp (cfzpModePhaseAbscissa W * ε) +
        Real.exp (-(cfzpModePhaseAbscissa W) * ε))

/-- The unnormalized cosine coefficient of the periodic carrier. -/
noncomputable def cfzp036LeadingCosCoeffNumerator
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  -cfzpModePhaseAbscissa W * Real.sin (W.rectangle.T * ε) *
      (Real.exp (cfzpModePhaseAbscissa W * ε) +
        Real.exp (-(cfzpModePhaseAbscissa W) * ε)) -
    W.rectangle.T * Real.cos (W.rectangle.T * ε) *
      (Real.exp (cfzpModePhaseAbscissa W * ε) -
        Real.exp (-(cfzpModePhaseAbscissa W) * ε))

/-- The leading carrier is a single sine/cosine pair. -/
theorem cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
    {ε u : ℝ} (_hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W u =
      (cfzp036LeadingSinCoeffNumerator ε W * Real.sin (W.rectangle.T * u) +
        cfzp036LeadingCosCoeffNumerator ε W * Real.cos (W.rectangle.T * u)) /
        ε := by
  unfold cfzp036PrimeAxisLeadingPeriodicCarrier
    cfzp036LeadingSinCoeffNumerator cfzp036LeadingCosCoeffNumerator
    cfzp036LinearPhaseCore
  have hl : W.rectangle.T * (u - ε) = W.rectangle.T * u - W.rectangle.T * ε := by
    ring
  have hr : W.rectangle.T * (u + ε) = W.rectangle.T * u + W.rectangle.T * ε := by
    ring
  rw [hl, hr, Real.sin_sub, Real.cos_sub, Real.sin_add, Real.cos_add]
  ring_nf

/-! ## Gate F: internal nontriviality of the carrier -/

/-- The coefficient square sum has an exact positive-factor form. -/
theorem cfzp036LeadingCoeff_sq_add_sq_eq_factor
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    (cfzp036LeadingSinCoeffNumerator ε W) ^ 2 +
        (cfzp036LeadingCosCoeffNumerator ε W) ^ 2 =
      (cfzpModePhaseAbscissa W ^ 2 + W.rectangle.T ^ 2) *
        (Real.cos (W.rectangle.T * ε) ^ 2 *
            (Real.exp (cfzpModePhaseAbscissa W * ε) -
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 +
          Real.sin (W.rectangle.T * ε) ^ 2 *
            (Real.exp (cfzpModePhaseAbscissa W * ε) +
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2) := by
  unfold cfzp036LeadingSinCoeffNumerator cfzp036LeadingCosCoeffNumerator
  ring

/-- The leading sine/cosine coefficient pair is internally nonzero. -/
theorem cfzp036LeadingCoeff_sq_add_sq_pos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 < (cfzp036LeadingSinCoeffNumerator ε W) ^ 2 +
        (cfzp036LeadingCosCoeffNumerator ε W) ^ 2 := by
  have ha : 0 < cfzpModePhaseAbscissa W := cfzpModePhaseAbscissa_pos W
  have hT : 0 < W.rectangle.T := W.rectangle.hT
  have hD : 0 < Real.exp (cfzpModePhaseAbscissa W * ε) -
      Real.exp (-(cfzpModePhaseAbscissa W) * ε) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_exp]
    nlinarith
  have hM : 0 < Real.exp (cfzpModePhaseAbscissa W * ε) +
      Real.exp (-(cfzpModePhaseAbscissa W) * ε) := by positivity
  have hDM : Real.exp (-(cfzpModePhaseAbscissa W) * ε) ≤
      Real.exp (cfzpModePhaseAbscissa W * ε) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hDsqM :
      (Real.exp (cfzpModePhaseAbscissa W * ε) -
          Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 ≤
        (Real.exp (cfzpModePhaseAbscissa W * ε) +
          Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 := by
    have hx : 0 ≤ Real.exp (cfzpModePhaseAbscissa W * ε) :=
      (Real.exp_pos _).le
    have hy : 0 ≤ Real.exp (-(cfzpModePhaseAbscissa W) * ε) :=
      (Real.exp_pos _).le
    nlinarith
  have hsecond : 0 <
      Real.cos (W.rectangle.T * ε) ^ 2 *
          (Real.exp (cfzpModePhaseAbscissa W * ε) -
            Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 +
        Real.sin (W.rectangle.T * ε) ^ 2 *
          (Real.exp (cfzpModePhaseAbscissa W * ε) +
            Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq (W.rectangle.T * ε)
    have hbase :
        (Real.exp (cfzpModePhaseAbscissa W * ε) -
            Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 =
          Real.cos (W.rectangle.T * ε) ^ 2 *
              (Real.exp (cfzpModePhaseAbscissa W * ε) -
                Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 +
            Real.sin (W.rectangle.T * ε) ^ 2 *
              (Real.exp (cfzpModePhaseAbscissa W * ε) -
                Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 := by
      nlinarith
    have hmono := mul_le_mul_of_nonneg_left hDsqM
      (sq_nonneg (Real.sin (W.rectangle.T * ε)))
    calc
      0 < (Real.exp (cfzpModePhaseAbscissa W * ε) -
          Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 :=
        sq_pos_of_pos hD
      _ = Real.cos (W.rectangle.T * ε) ^ 2 *
            (Real.exp (cfzpModePhaseAbscissa W * ε) -
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 +
          Real.sin (W.rectangle.T * ε) ^ 2 *
            (Real.exp (cfzpModePhaseAbscissa W * ε) -
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 := hbase
      _ ≤ Real.cos (W.rectangle.T * ε) ^ 2 *
            (Real.exp (cfzpModePhaseAbscissa W * ε) -
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 +
          Real.sin (W.rectangle.T * ε) ^ 2 *
            (Real.exp (cfzpModePhaseAbscissa W * ε) +
              Real.exp (-(cfzpModePhaseAbscissa W) * ε)) ^ 2 := by
        exact add_le_add_right hmono _
  rw [cfzp036LeadingCoeff_sq_add_sq_eq_factor]
  exact mul_pos (by positivity) hsecond

/-- The carrier is not the zero function. -/
theorem cfzp036LeadingCoeff_pair_ne_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp036LeadingSinCoeffNumerator ε W ≠ 0 ∨
      cfzp036LeadingCosCoeffNumerator ε W ≠ 0 := by
  by_contra h
  have hsin : cfzp036LeadingSinCoeffNumerator ε W = 0 := by
    by_contra hsin
    exact h (Or.inl hsin)
  have hcos : cfzp036LeadingCosCoeffNumerator ε W = 0 := by
    by_contra hcos
    exact h (Or.inr hcos)
  have hzero := cfzp036LeadingCoeff_sq_add_sq_pos hε W
  rw [hsin, hcos, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_add] at hzero
  exact (lt_irrefl 0) hzero

/-! ## Gate G: explicit period -/

/-- The coordinate period of the leading carrier. -/
noncomputable def cfzp036PrimeAxisCarrierPeriod
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  2 * Real.pi / W.rectangle.T

/-- The period is positive. -/
theorem cfzp036PrimeAxisCarrierPeriod_pos
    (W : PascalCenteredXiResidueTransportWindow) :
    0 < cfzp036PrimeAxisCarrierPeriod W := by
  unfold cfzp036PrimeAxisCarrierPeriod
  exact div_pos (by positivity) W.rectangle.hT

/-- The leading carrier is periodic with period `2π / T`. -/
theorem cfzp036PrimeAxisLeadingPeriodicCarrier_periodic
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (u + cfzp036PrimeAxisCarrierPeriod W) =
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u := by
  unfold cfzp036PrimeAxisLeadingPeriodicCarrier
    cfzp036PrimeAxisCarrierPeriod
    cfzp036LinearPhaseCore
  have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
  have hleft : W.rectangle.T *
      (u + 2 * Real.pi / W.rectangle.T - ε) =
      W.rectangle.T * (u - ε) + 2 * Real.pi := by
    field_simp [hT]
    ring
  have hright : W.rectangle.T *
      (u + 2 * Real.pi / W.rectangle.T + ε) =
      W.rectangle.T * (u + ε) + 2 * Real.pi := by
    field_simp [hT]
    ring
  simp only [hleft, hright, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-! ## Gate H: finite carrier-margin transport -/

/-- A finite constant for the `K / u` remainder envelope. -/
noncomputable def cfzp036PrimeAxisRemainderConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (2 * Real.exp ((cfzpModePhaseAbscissa W) * ε) +
      Real.exp (-(cfzpModePhaseAbscissa W) * ε)) *
      (cfzpModePhaseAbscissa W + W.rectangle.T) +
    (4 * Real.exp ((cfzpModePhaseAbscissa W) * ε) +
      Real.exp (-(cfzpModePhaseAbscissa W) * ε)) / ε

/-- The remainder constant is positive on the safe finite regime. -/
theorem cfzp036PrimeAxisRemainderConstant_pos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 < cfzp036PrimeAxisRemainderConstant ε W := by
  unfold cfzp036PrimeAxisRemainderConstant
  have ha : 0 < cfzpModePhaseAbscissa W := cfzpModePhaseAbscissa_pos W
  have hT : 0 < W.rectangle.T := W.rectangle.hT
  positivity

/-- The exact remainder admits a prime-independent finite `K / u` envelope. -/
theorem cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div
    {ε u : ℝ} (hε : 0 < ε) (hu : 1 ≤ u) (h2ε : 2 * ε ≤ u)
    (W : PascalCenteredXiResidueTransportWindow) :
    |cfzp036PrimeAxisAmplitudeRemainder ε W u| ≤
      cfzp036PrimeAxisRemainderConstant ε W / u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < u - ε := by linarith
  have hr : 0 < u + ε := by linarith
  have hInvL : 1 / (u - ε) ≤ 2 / u := by
    apply (div_le_div_iff₀ hl hu0).2
    linarith
  have hInvR : 1 / (u + ε) ≤ 1 / u := by
    apply (div_le_div_iff₀ hr hu0).2
    linarith
  have hUL : u / (u - ε) ≤ 2 := by
    apply (div_le_iff₀ hl).2
    linarith
  have hUR : u / (u + ε) ≤ 1 := by
    apply (div_le_iff₀ hr).2
    linarith
  have hUL2 : u / (u - ε) ^ 2 ≤ 4 / u := by
    calc
      u / (u - ε) ^ 2 = (1 / (u - ε)) * (u / (u - ε)) := by
        field_simp [hl.ne']
      _ ≤ (2 / u) * 2 := by
        exact mul_le_mul hInvL hUL (by positivity) (by positivity)
      _ = 4 / u := by ring
  have hUR2 : u / (u + ε) ^ 2 ≤ 1 / u := by
    calc
      u / (u + ε) ^ 2 = (1 / (u + ε)) * (u / (u + ε)) := by
        field_simp [hr.ne']
      _ ≤ (1 / u) * 1 := by
        exact mul_le_mul hInvR hUR (by positivity) (by positivity)
      _ = 1 / u := by ring
  have hgeneric : ∀ {E F P Q s t B : ℝ},
      0 ≤ E → 0 ≤ F → 0 ≤ B → |P| ≤ B → |Q| ≤ B →
      |s| ≤ 1 → |t| ≤ 1 →
      |E / (u - ε) * P + F / (u + ε) * Q +
          (u / ε) * (E / (u - ε) ^ 2 * s -
            F / (u + ε) ^ 2 * t)| ≤
        ((2 * E + F) * B + (4 * E + F) / ε) / u := by
    intro E F P Q s t B hE hF hB hP hQ hs ht
    have hEdiv : E / (u - ε) ≤ 2 * E / u := by
      calc
        E / (u - ε) = E * (1 / (u - ε)) := by ring
        _ ≤ E * (2 / u) := mul_le_mul_of_nonneg_left hInvL hE
        _ = 2 * E / u := by ring
    have hFdiv : F / (u + ε) ≤ F / u := by
      calc
        F / (u + ε) = F * (1 / (u + ε)) := by ring
        _ ≤ F * (1 / u) := mul_le_mul_of_nonneg_left hInvR hF
        _ = F / u := by ring
    have hone :
        |E / (u - ε) * P| ≤ 2 * E * B / u := by
      rw [abs_mul, abs_div, abs_of_nonneg hE, abs_of_pos hl]
      calc
        E / (u - ε) * |P| ≤ E / (u - ε) * B :=
          mul_le_mul_of_nonneg_left hP (by positivity)
        _ ≤ (2 * E / u) * B :=
          mul_le_mul_of_nonneg_right hEdiv hB
        _ = 2 * E * B / u := by ring
    have htwo :
        |F / (u + ε) * Q| ≤ F * B / u := by
      rw [abs_mul, abs_div, abs_of_nonneg hF, abs_of_pos hr]
      calc
        F / (u + ε) * |Q| ≤ F / (u + ε) * B :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
        _ ≤ (F / u) * B :=
          mul_le_mul_of_nonneg_right hFdiv hB
        _ = F * B / u := by ring
    have hthreeL :
        |(u / ε) * (E / (u - ε) ^ 2 * s)| ≤ 4 * E / (ε * u) := by
      rw [abs_mul, abs_of_pos (div_pos hu0 hε), abs_mul, abs_div,
        abs_of_nonneg hE, abs_of_pos (sq_pos_of_pos hl)]
      calc
        u / ε * (E / (u - ε) ^ 2 * |s|) ≤
            u / ε * (E / (u - ε) ^ 2 * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
        _ = (E / ε) * (u / (u - ε) ^ 2) := by
          field_simp [hε.ne', hl.ne']
        _ ≤ (E / ε) * (4 / u) :=
          mul_le_mul_of_nonneg_left hUL2 (by positivity)
        _ = 4 * E / (ε * u) := by
          field_simp [hε.ne', hu0.ne']
    have hthreeR :
        |(u / ε) * (F / (u + ε) ^ 2 * t)| ≤ F / (ε * u) := by
      rw [abs_mul, abs_of_pos (div_pos hu0 hε), abs_mul, abs_div,
        abs_of_nonneg hF, abs_of_pos (sq_pos_of_pos hr)]
      calc
        u / ε * (F / (u + ε) ^ 2 * |t|) ≤
            u / ε * (F / (u + ε) ^ 2 * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ht (by positivity)) (by positivity)
        _ = (F / ε) * (u / (u + ε) ^ 2) := by
          field_simp [hε.ne', hr.ne']
        _ ≤ (F / ε) * (1 / u) :=
          mul_le_mul_of_nonneg_left hUR2 (by positivity)
        _ = F / (ε * u) := by
          field_simp [hε.ne', hu0.ne']
    have hthree :
        |(u / ε) * (E / (u - ε) ^ 2 * s -
            F / (u + ε) ^ 2 * t)| ≤ (4 * E + F) / (ε * u) := by
      rw [abs_mul, abs_of_pos (div_pos hu0 hε)]
      calc
        u / ε * |E / (u - ε) ^ 2 * s -
            F / (u + ε) ^ 2 * t| ≤
            u / ε * (|E / (u - ε) ^ 2 * s| +
              |F / (u + ε) ^ 2 * t|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
        _ = |(u / ε) * (E / (u - ε) ^ 2 * s)| +
            |(u / ε) * (F / (u + ε) ^ 2 * t)| := by
          simp only [abs_mul, abs_div, abs_of_pos (div_pos hu0 hε),
            abs_of_nonneg hE, abs_of_nonneg hF,
            abs_of_pos (sq_pos_of_pos hl), abs_of_pos (sq_pos_of_pos hr)]
          ring
        _ ≤ 4 * E / (ε * u) + F / (ε * u) :=
          add_le_add hthreeL hthreeR
        _ = (4 * E + F) / (ε * u) := by ring
    calc
      |E / (u - ε) * P + F / (u + ε) * Q +
          (u / ε) * (E / (u - ε) ^ 2 * s -
            F / (u + ε) ^ 2 * t)| ≤
          |E / (u - ε) * P + F / (u + ε) * Q| +
            |(u / ε) * (E / (u - ε) ^ 2 * s -
              F / (u + ε) ^ 2 * t)| := by
        exact abs_add_le _ _
      _ ≤ (|E / (u - ε) * P| + |F / (u + ε) * Q|) +
          |(u / ε) * (E / (u - ε) ^ 2 * s -
            F / (u + ε) ^ 2 * t)| := by
        simpa only [add_assoc, add_comm, add_left_comm] using
          (add_le_add_right (abs_add_le
            (E / (u - ε) * P) (F / (u + ε) * Q))
            |(u / ε) * (E / (u - ε) ^ 2 * s -
              F / (u + ε) ^ 2 * t)|)
      _ ≤ (2 * E * B / u + F * B / u) +
          (4 * E + F) / (ε * u) := by
        exact add_le_add (add_le_add hone htwo) hthree
      _ = ((2 * E + F) * B + (4 * E + F) / ε) / u := by
        field_simp [hε.ne', hu0.ne']
  unfold cfzp036PrimeAxisAmplitudeRemainder cfzp036PrimeAxisRemainderConstant
  apply hgeneric
  · positivity
  · positivity
  · exact add_nonneg (cfzpModePhaseAbscissa_pos W).le W.rectangle.hT.le
  · exact cfzp036LinearPhaseCore_abs_le
      (cfzpModePhaseAbscissa_pos W).le W.rectangle.hT.le
  · exact cfzp036LinearPhaseCore_abs_le
      (cfzpModePhaseAbscissa_pos W).le W.rectangle.hT.le
  · apply abs_le.mpr
    exact ⟨Real.neg_one_le_sin (W.rectangle.T * (u - ε)),
      Real.sin_le_one (W.rectangle.T * (u - ε))⟩
  · apply abs_le.mpr
    exact ⟨Real.neg_one_le_sin (W.rectangle.T * (u + ε)),
      Real.sin_le_one (W.rectangle.T * (u + ε))⟩

/-- Positive carrier margin dominates the exact amplitude at finite scale. -/
theorem cfzp036PrimeAxisCoordinateAmplitude_ge_half_of_le_leading
    {ε κ u : ℝ} (hε : 0 < ε) (hu : 1 ≤ u) (h2ε : 2 * ε ≤ u)
    (_hκ : 0 < κ)
    (W : PascalCenteredXiResidueTransportWindow)
    (hmargin : κ ≤ cfzp036PrimeAxisLeadingPeriodicCarrier ε W u)
    (hrem : cfzp036PrimeAxisRemainderConstant ε W / u ≤ κ / 2)
    :
    κ / 2 ≤ cfzp036PrimeAxisCoordinateAmplitude ε W u := by
  have hlpos : 0 < u - ε := by nlinarith
  have hrpos : 0 < u + ε := by nlinarith
  have hdecomp := cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder
    hε.ne' hlpos.ne' hrpos.ne' W
  have habs := cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div
    hε hu h2ε W
  rw [hdecomp]
  have hlow : -κ / 2 ≤ cfzp036PrimeAxisAmplitudeRemainder ε W u := by
    have := (abs_le.mp habs).1
    linarith
  linarith

/-- Negative carrier margin dominates the exact amplitude at finite scale. -/
theorem cfzp036PrimeAxisCoordinateAmplitude_le_neg_half_of_le_leading
    {ε κ u : ℝ} (hε : 0 < ε) (hu : 1 ≤ u) (h2ε : 2 * ε ≤ u)
    (_hκ : 0 < κ)
    (W : PascalCenteredXiResidueTransportWindow)
    (hmargin : cfzp036PrimeAxisLeadingPeriodicCarrier ε W u ≤ -κ)
    (hrem : cfzp036PrimeAxisRemainderConstant ε W / u ≤ κ / 2)
    :
    cfzp036PrimeAxisCoordinateAmplitude ε W u ≤ -κ / 2 := by
  have hlpos : 0 < u - ε := by nlinarith
  have hrpos : 0 < u + ε := by nlinarith
  have hdecomp := cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder
    hε.ne' hlpos.ne' hrpos.ne' W
  have habs := cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div
    hε hu h2ε W
  rw [hdecomp]
  have hupp : cfzp036PrimeAxisAmplitudeRemainder ε W u ≤ κ / 2 := by
    have := (abs_le.mp habs).2
    linarith
  linarith

/-! ## Firewall -/

inductive Cfzp036PrimeAxisSigmaStrippedPeriodicCarrierGap : Prop
  | noPrimeLogCarrierArcHitProvider
  | noPrimeAxisWeightedSignedCarrierDominanceProvider
  | noExceptionalHigherPowerResidualElimination
  | noAutomaticSubcriticalWindowProvider

end DkMath.RH.CFBRCProjection
