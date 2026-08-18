/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaAdditiveCircleIrrationalRotationCofinalHitAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaUniversalPrimePowerBadDebtEnvelopeAudit"

/-!
# CFZP-029: universal prime-power bad-debt envelope

This module closes the analytic Bad-side input left open by CFZP-027.  The
left endpoint of a centered frequency cell gives a prefactor ceiling, while a
right endpoint angle gives a universal absolute bound for the dimensionless
phase derivative core.  These two finite formulas produce automatic event,
pulse, and negative-debt bounds for every safe prime power.

The critical scale is the existing
`cfzpModeCriticalScale n = exp (-(1 / 2) * log n)`, so its prime-power
specialization decays with the exponent.  This file does not assert that the
resulting Bad debt is dominated by Good credit, nor does it provide any
infinite-sum, limit, or RH conclusion.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set
open DkMath.NumberTheory

/-! ## Gate A: the left-endpoint prefactor ceiling -/

/-- The left-endpoint upper bound for the centered derivative prefactor. -/
noncomputable def cfzp029CenteredDerivativePrefactorCeiling
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  let l := cfzpPrimePowerPhaseMagnitudeLeft ε p j
  Real.exp (-(cfzpModePhaseAbscissa W) * l) / l ^ 3

/-- The ceiling is positive on every safe prime-power cell. -/
theorem cfzp029CenteredDerivativePrefactorCeiling_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp029CenteredDerivativePrefactorCeiling ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  unfold cfzp029CenteredDerivativePrefactorCeiling
  dsimp
  exact div_pos (Real.exp_pos _) (pow_pos hmag.1 3)

/-- The exact positive prefactor is bounded by the left-endpoint ceiling. -/
theorem cfzp029CenteredDerivativePrefactor_le_ceiling
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {u : ℝ} (hu : u ∈ Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j)) :
    Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 ≤
      cfzp029CenteredDerivativePrefactorCeiling ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have ha : 0 ≤ cfzpModePhaseAbscissa W :=
    (cfzpModePhaseAbscissa_pos W).le
  have huPos : 0 < u := lt_trans hmag.1 hu.1
  have hpow :
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j) ^ 3 ≤ u ^ 3 := by
    exact pow_le_pow_left₀ hmag.1.le hu.1.le 3
  have hexp : Real.exp (-(cfzpModePhaseAbscissa W) * u) ≤
      Real.exp (-(cfzpModePhaseAbscissa W) *
        cfzpPrimePowerPhaseMagnitudeLeft ε p j) := by
    apply Real.exp_le_exp.mpr
    simpa [neg_mul] using
      (neg_le_neg (mul_le_mul_of_nonneg_left hu.1.le ha))
  unfold cfzp029CenteredDerivativePrefactorCeiling
  dsimp
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 ≤
        Real.exp (-(cfzpModePhaseAbscissa W) *
          cfzpPrimePowerPhaseMagnitudeLeft ε p j) / u ^ 3 := by
      exact div_le_div_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (-(cfzpModePhaseAbscissa W) *
          cfzpPrimePowerPhaseMagnitudeLeft ε p j) /
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j) ^ 3 := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le
        (pow_pos hmag.1 3) hpow

/-! ## Gate B: a universal dimensionless core envelope -/

/-- A right-endpoint polynomial envelope for the phase derivative core. -/
noncomputable def cfzp029PhaseDerivativeCoreAbsEnvelope
    (α R : ℝ) : ℝ :=
  R ^ 2 * |1 - α ^ 2| +
    2 * (α * R + 1) +
    2 * R * (α * R + 1)

private theorem cfzp029PhaseDerivativeSinCoeff_abs_le
    {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 ≤ θ) :
    |cfzpPhaseDerivativeSinCoeff α θ| ≤
      θ ^ 2 * |1 - α ^ 2| + 2 * (α * θ + 1) := by
  have hcoef : 0 ≤ α * θ + 1 := by positivity
  unfold cfzpPhaseDerivativeSinCoeff
  calc
    |θ ^ 2 * (1 - α ^ 2) - 2 * (α * θ + 1)| ≤
        |θ ^ 2 * (1 - α ^ 2)| + |2 * (α * θ + 1)| :=
      by
        have h := abs_sub_le
          (θ ^ 2 * (1 - α ^ 2)) 0 (2 * (α * θ + 1))
        simpa using h
    _ = θ ^ 2 * |1 - α ^ 2| + 2 * (α * θ + 1) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg θ), abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hcoef]

/-- The universal envelope is nonnegative for nonnegative aspect ratio. -/
theorem cfzp029PhaseDerivativeCoreAbsEnvelope_nonneg
    {α R : ℝ} (hα : 0 ≤ α) (hR : 0 ≤ R) :
    0 ≤ cfzp029PhaseDerivativeCoreAbsEnvelope α R := by
  unfold cfzp029PhaseDerivativeCoreAbsEnvelope
  positivity

/-- The phase derivative core is bounded without a subcriticality assumption. -/
theorem cfzp029PhaseDerivativeCore_abs_le
    {α R θ : ℝ} (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hθR : θ ≤ R) :
    |cfzpPhaseDerivativeCore α θ| ≤
      cfzp029PhaseDerivativeCoreAbsEnvelope α R := by
  have hcoefθ : 0 ≤ α * θ + 1 := by positivity
  have hR : 0 ≤ R := le_trans hθ hθR
  have hcoefR : 0 ≤ α * R + 1 := by positivity
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hsinCoeff := cfzp029PhaseDerivativeSinCoeff_abs_le hα hθ
  have hcore : |cfzpPhaseDerivativeCore α θ| ≤
      θ ^ 2 * |1 - α ^ 2| + 2 * (α * θ + 1) +
        2 * θ * (α * θ + 1) := by
    unfold cfzpPhaseDerivativeCore
    calc
      |cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ +
          2 * θ * (α * θ + 1) * Real.cos θ| ≤
          |cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ| +
            |2 * θ * (α * θ + 1) * Real.cos θ| := abs_add_le _ _
      _ = |cfzpPhaseDerivativeSinCoeff α θ| * |Real.sin θ| +
          |2 * θ * (α * θ + 1)| * |Real.cos θ| := by
        rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |cfzpPhaseDerivativeSinCoeff α θ| * 1 +
          |2 * θ * (α * θ + 1)| * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsin (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hcos (abs_nonneg _))
      _ = |cfzpPhaseDerivativeSinCoeff α θ| + 2 * θ * (α * θ + 1) := by
        have hterm : 0 ≤ 2 * θ * (α * θ + 1) := by positivity
        rw [abs_of_nonneg hterm]
        ring
      _ ≤ θ ^ 2 * |1 - α ^ 2| + 2 * (α * θ + 1) +
          2 * θ * (α * θ + 1) := by
        convert add_le_add_right hsinCoeff
          (2 * θ * (α * θ + 1)) using 1 <;> ring
  have hsq : θ ^ 2 ≤ R ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hθR) (add_nonneg hθ hR)]
  have hlin : α * θ + 1 ≤ α * R + 1 := by
    linarith [mul_le_mul_of_nonneg_left hθR hα]
  have hfirst : θ ^ 2 * |1 - α ^ 2| ≤
      R ^ 2 * |1 - α ^ 2| :=
    mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
  have hsecond : 2 * (α * θ + 1) ≤ 2 * (α * R + 1) :=
    mul_le_mul_of_nonneg_left hlin (by norm_num)
  have hthird₁ : 2 * θ * (α * θ + 1) ≤
      2 * R * (α * θ + 1) := by
    calc
      2 * θ * (α * θ + 1) = 2 * (θ * (α * θ + 1)) := by ring
      _ ≤ 2 * (R * (α * θ + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hθR hcoefθ) (by norm_num)
      _ = 2 * R * (α * θ + 1) := by ring
  have hthird₂ : 2 * R * (α * θ + 1) ≤
      2 * R * (α * R + 1) := by
    exact mul_le_mul_of_nonneg_left hlin (by positivity : 0 ≤ 2 * R)
  unfold cfzp029PhaseDerivativeCoreAbsEnvelope
  calc
    |cfzpPhaseDerivativeCore α θ| ≤
        θ ^ 2 * |1 - α ^ 2| + 2 * (α * θ + 1) +
          2 * θ * (α * θ + 1) := hcore
    _ ≤ R ^ 2 * |1 - α ^ 2| + 2 * (α * R + 1) +
          2 * R * (α * R + 1) := by
      exact add_le_add (add_le_add hfirst hsecond) (hthird₁.trans hthird₂)

/-! ## Gate C: transport to a centered prime-power cell -/

/-- The frequency derivative core is bounded by the right endpoint angle. -/
theorem cfzp029CenteredDerivativeCore_abs_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {u : ℝ} (hu : u ∈ Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j)) :
    |cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u| ≤
      cfzp029PhaseDerivativeCoreAbsEnvelope
        (cfzpModePhaseAspectRatio W)
        (cfzpPrimePowerPhaseAngleRight ε W p j) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have huPos : 0 < u := lt_trans hmag.1 hu.1
  have hθ0 : 0 ≤ u * W.rectangle.T :=
    mul_nonneg huPos.le W.rectangle.hT.le
  have hθR : u * W.rectangle.T ≤
      cfzpPrimePowerPhaseAngleRight ε W p j := by
    rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hu.2.le W.rectangle.hT.le)
  rw [cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
    (a := cfzpModePhaseAbscissa W) (T := W.rectangle.T) (u := u)
    W.rectangle.hT.ne']
  exact cfzp029PhaseDerivativeCore_abs_le
    (cfzpModePhaseAspectRatio_pos W).le hθ0 hθR

/-! ## Gate D: the automatic centered derivative envelope -/

/-- The explicit absolute derivative bound for a safe prime power. -/
noncomputable def cfzp029CenteredProfileDerivativeAbsBound
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp029CenteredDerivativePrefactorCeiling ε W p j *
    cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j)

/-- The automatic derivative bound is nonnegative. -/
theorem cfzp029CenteredProfileDerivativeAbsBound_nonneg
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 ≤ cfzp029CenteredProfileDerivativeAbsBound ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hR : 0 ≤ cfzpPrimePowerPhaseAngleRight ε W p j := by
    rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
    exact mul_nonneg W.rectangle.hT.le hmag.2.le
  exact mul_nonneg
    (cfzp029CenteredDerivativePrefactorCeiling_pos hε hε2 W hp hj).le
    (cfzp029PhaseDerivativeCoreAbsEnvelope_nonneg
      (cfzpModePhaseAspectRatio_pos W).le
      hR)

/-- The automatic bound fills the CFZP-023 derivative-envelope contract. -/
theorem cfzp029CenteredProfileDerivativeAbsBound_envelope
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    Cfzp023CenteredProfileDerivativeAbsEnvelope ε W p j
      (cfzp029CenteredProfileDerivativeAbsBound ε W p j) := by
  intro u hu
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have huPos : 0 < u := lt_trans hmag.1 hu.1
  have hpref : 0 ≤ Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 :=
    (cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos huPos).le
  have hceil := cfzp029CenteredDerivativePrefactor_le_ceiling
    hε hε2 W hp hj hu
  have hcore := cfzp029CenteredDerivativeCore_abs_le hε hε2 W hp hj hu
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv huPos.ne', abs_mul,
    abs_of_nonneg hpref]
  unfold cfzp029CenteredProfileDerivativeAbsBound
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 *
          |cfzpNegativeFrequencyBoundaryProfileDerivativeCore
            (cfzpModePhaseAbscissa W) W.rectangle.T u| ≤
        Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 *
          cfzp029PhaseDerivativeCoreAbsEnvelope
            (cfzpModePhaseAspectRatio W)
            (cfzpPrimePowerPhaseAngleRight ε W p j) :=
      mul_le_mul_of_nonneg_left hcore hpref
    _ ≤ cfzp029CenteredDerivativePrefactorCeiling ε W p j *
          cfzp029PhaseDerivativeCoreAbsEnvelope
            (cfzpModePhaseAspectRatio W)
            (cfzpPrimePowerPhaseAngleRight ε W p j) :=
      mul_le_mul_of_nonneg_right hceil
        (cfzp029PhaseDerivativeCoreAbsEnvelope_nonneg
          (cfzpModePhaseAspectRatio_pos W).le
          (by
            have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
              hε hε2 hp hj
            rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
            exact mul_nonneg W.rectangle.hT.le hmag.2.le))

/-! ## Gate E: automatic event, pulse, and debt bounds -/

/-- The explicit one-prime-power Bad-debt ceiling. -/
noncomputable def cfzp029PrimePowerBadDebtEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
    cfzp029CenteredProfileDerivativeAbsBound ε W p j

/-- The one-prime-power debt ceiling is nonnegative. -/
theorem cfzp029PrimePowerBadDebtEnvelope_nonneg
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 ≤ cfzp029PrimePowerBadDebtEnvelope ε W p j := by
  unfold cfzp029PrimePowerBadDebtEnvelope
  have hlog : 0 ≤ Real.log (p : ℝ) := by
    exact (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hlog)
      (cfzpModeCriticalScale_pos (p ^ j)).le)
    (cfzp029CenteredProfileDerivativeAbsBound_nonneg hε hε2 W hp hj)

/-- The branch-free prime-power event obeys the automatic ceiling. -/
theorem cfzp029PrimePowerBranchFreeTrigEvent_abs_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    |cfzpPrimePowerBranchFreeTrigEvent ε W p j| ≤
      cfzp029PrimePowerBadDebtEnvelope ε W p j := by
  unfold cfzp029PrimePowerBadDebtEnvelope
  exact cfzp023PrimePowerBranchFreeTrigEvent_abs_le_quantitativeEnvelope
    hε hε2 W hp hj
    (cfzp029CenteredProfileDerivativeAbsBound_nonneg hε hε2 W hp hj)
    (cfzp029CenteredProfileDerivativeAbsBound_envelope hε hε2 W hp hj)

/-- The canonical negative event debt obeys the automatic ceiling. -/
theorem cfzp029PrimePowerEventNegativeDebt_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzp019PrimePowerEventNegativeDebt ε W p j ≤
      cfzp029PrimePowerBadDebtEnvelope ε W p j := by
  unfold cfzp029PrimePowerBadDebtEnvelope
  exact cfzp023PrimePowerEventNegativeDebt_le_quantitativeEnvelope
    hε hε2 W hp hj
    (cfzp029CenteredProfileDerivativeAbsBound_nonneg hε hε2 W hp hj)
    (cfzp029CenteredProfileDerivativeAbsBound_envelope hε hε2 W hp hj)

/-- The automatic ceiling transports to a prime-power von-Mangoldt pulse. -/
theorem cfzp029VonMangoldtPulse_abs_le_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j) :
    |cfzp021VonMangoldtPulse ε W n| ≤
      cfzp029PrimePowerBadDebtEnvelope ε W p j := by
  unfold cfzp029PrimePowerBadDebtEnvelope
  exact cfzp023VonMangoldtPulse_abs_le_quantitativeEnvelope_of_eq_prime_pow
    hε hε2 W hp hj hn
    (cfzp029CenteredProfileDerivativeAbsBound_nonneg hε hε2 W hp hj)
    (cfzp029CenteredProfileDerivativeAbsBound_envelope hε hε2 W hp hj)

/-! ## Gate F: an automatic finite Bad-debt sum -/

/-- The explicit finite debt envelope on an arbitrary Bad support. -/
noncomputable def cfzp029AutomaticBadDebtEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (Bad : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ Bad, cfzp029PrimePowerBadDebtEnvelope ε W pk.1 (pk.2 + 1)

private theorem cfzp029_prime_and_positive_exponent
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

/-- Every finite block Bad debt is bounded by its automatic explicit sum. -/
theorem cfzp029AutomaticBadDebtEnvelope_sum_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    {Bad : Finset (ℕ × ℕ)}
    (hBad : Bad ⊆ cfzp024PrimePowerPairBlockSupport A B) :
    (∑ pk ∈ Bad,
      cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1)) ≤
      cfzp029AutomaticBadDebtEnvelope ε W Bad := by
  unfold cfzp029AutomaticBadDebtEnvelope
  apply Finset.sum_le_sum
  intro pk hpk
  have hpair := cfzp029_prime_and_positive_exponent hAB (hBad hpk)
  exact cfzp029PrimePowerEventNegativeDebt_le
    hε hε2 W hpair.1 hpair.2

/-! ## Gate G: CFZP-027 constructor with no Bad analytic inputs -/

/-- Build a certified finite block while supplying Bad envelopes automatically. -/
noncomputable def cfzp029FiniteBlockCertificate_of_subcriticalReadyHits
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk)) :
    Cfzp024FiniteBlockCertificate ε W A B := by
  let K : ℕ × ℕ → ℝ := fun pk =>
    cfzp029CenteredProfileDerivativeAbsBound ε W pk.1 (pk.2 + 1)
  refine cfzp027FiniteBlockCertificate_of_subcriticalReadyHits
    hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready K ?_ ?_
  · intro pk hpk
    have hpair := cfzp029_prime_and_positive_exponent hAB
      (cfzp024Bad_subset_block Good hpk)
    exact (cfzp029CenteredProfileDerivativeAbsBound_nonneg
      hε hε2 W hpair.1 hpair.2)
  · intro pk hpk
    have hpair := cfzp029_prime_and_positive_exponent hAB
      (cfzp024Bad_subset_block Good hpk)
    exact cfzp029CenteredProfileDerivativeAbsBound_envelope
      hε hε2 W hpair.1 hpair.2

/-! ## Firewall -/

/-- The automatic envelope does not provide a weighted dominance theorem. -/
inductive Cfzp029UniversalPrimePowerBadDebtEnvelopeGap : Prop
  | noIndependentWeightedCreditDebtDominanceProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider

end DkMath.RH.CFBRCProjection
