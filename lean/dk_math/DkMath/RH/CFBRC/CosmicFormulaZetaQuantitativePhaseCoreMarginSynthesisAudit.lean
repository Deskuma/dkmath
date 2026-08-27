/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaCertifiedBlockCreditDebtDominanceAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePhaseCoreMarginSynthesisAudit"

/-!
# CFZP-025: quantitative phase-core margin synthesis

This module exposes the analytic content of a CFZP-024 Good certificate.
Quantitative negativity of the dimensionless phase core is transported to the
frequency derivative core, multiplied by an explicit finite-interval
prefactor floor, and then fed to the CFZP-023 event and CFZP-024 certificate
interfaces.  Phase-cell coverage and cofinal dominance remain hypotheses.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Set

private theorem cfzp025_prime_and_positive_exponent
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

/-! ## Gate A: centered prefactor floor -/

/-- The right-endpoint floor for the positive profile derivative prefactor. -/
noncomputable def cfzp025CenteredDerivativePrefactorFloor
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  let r := cfzpPrimePowerPhaseMagnitudeRight ε p j
  Real.exp (-(cfzpModePhaseAbscissa W) * r) / r ^ 3

/-- The prefactor floor is strictly positive in the safe-frequency regime. -/
theorem cfzp025CenteredDerivativePrefactorFloor_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp025CenteredDerivativePrefactorFloor ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  unfold cfzp025CenteredDerivativePrefactorFloor
  dsimp
  exact div_pos (Real.exp_pos _) (pow_pos hmag.2 3)

/-- On the centered frequency interval, the right-endpoint prefactor floor
is below the exact positive derivative prefactor. -/
theorem cfzp025CenteredDerivativePrefactorFloor_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {u : ℝ} (hu : u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j)) :
    cfzp025CenteredDerivativePrefactorFloor ε W p j ≤
      Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have ha : 0 ≤ cfzpModePhaseAbscissa W :=
    (cfzpModePhaseAbscissa_pos W).le
  have huPos : 0 < u := lt_trans hmag.1 hu.1
  have hpow : u ^ 3 ≤
      (cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
    exact pow_le_pow_left₀ huPos.le hu.2.le 3
  have hexp : Real.exp
        (-(cfzpModePhaseAbscissa W) *
          cfzpPrimePowerPhaseMagnitudeRight ε p j) ≤
      Real.exp (-(cfzpModePhaseAbscissa W) * u) := by
    apply Real.exp_le_exp.mpr
    simpa [neg_mul] using
      (neg_le_neg (mul_le_mul_of_nonneg_left hu.2.le ha))
  unfold cfzp025CenteredDerivativePrefactorFloor
  dsimp
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) *
        cfzpPrimePowerPhaseMagnitudeRight ε p j) /
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 ≤
      Real.exp (-(cfzpModePhaseAbscissa W) * u) /
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
          exact div_le_div_of_nonneg_right hexp (pow_pos hmag.2 3).le
    _ ≤ Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hpow

/-! ## Gate B/C: phase-core margin and frequency transport -/

/-- A uniform negative margin for the dimensionless phase core on the
centered angular interval. -/
def Cfzp025CenteredPhaseCoreNegativeMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) (δ : ℝ) : Prop :=
  ∀ θ ∈ Set.Ioo
      (cfzpPrimePowerPhaseAngleLeft ε W p j)
      (cfzpPrimePowerPhaseAngleRight ε W p j),
    cfzpPhaseDerivativeCore (cfzpModePhaseAspectRatio W) θ ≤ -δ

/-- A phase-core margin transports to the original frequency derivative core. -/
theorem cfzp025DerivativeCore_le_neg_of_phaseCoreMargin
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {δ : ℝ} (_hδ : 0 ≤ δ)
    (hphase : Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ) :
    ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u ≤ -δ := by
  have hangles := cfzpPrimePowerPhaseAngles_pos_of_epsilon_lt_log_two
    hε hε2 W hp hj
  have hT := W.rectangle.hT
  intro u hu
  have hθ : u * W.rectangle.T ∈ Set.Ioo
      (cfzpPrimePowerPhaseAngleLeft ε W p j)
      (cfzpPrimePowerPhaseAngleRight ε W p j) := by
    rw [cfzpPrimePowerPhaseAngleLeft_eq_rectangleT_mul_phaseMagnitudeLeft,
      cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
    constructor <;> nlinarith [hT, hu.1, hu.2]
  rw [cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
    (a := cfzpModePhaseAbscissa W) (T := W.rectangle.T) (u := u) hT.ne']
  simpa [cfzpModePhaseAspectRatio] using hphase (u * W.rectangle.T) hθ

/-! ## Gate D: phase margin to profile derivative margin -/

/-- A phase-core margin supplies the derivative-level margin required by
CFZP-023, with the explicit right-endpoint prefactor floor. -/
theorem cfzp025CenteredProfileDerivativeDropMargin_of_phaseCoreMargin
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hphase : Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ) :
    Cfzp023CenteredProfileDerivativeDropMargin ε W p j
      (cfzp025CenteredDerivativePrefactorFloor ε W p j * δ) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hcore := cfzp025DerivativeCore_le_neg_of_phaseCoreMargin
    hε hε2 W hp hj hδ hphase
  have hfloorPos := cfzp025CenteredDerivativePrefactorFloor_pos
    hε hε2 W hp hj
  intro u hu
  have hfloor := cfzp025CenteredDerivativePrefactorFloor_le
    hε hε2 W hp hj (u := u) hu
  have huPos : 0 < u := lt_trans hmag.1 hu.1
  have hprefPos : 0 ≤ Real.exp
      (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 :=
    (cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos huPos).le
  have hmul₁ :
      (Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3) *
          cfzpNegativeFrequencyBoundaryProfileDerivativeCore
            (cfzpModePhaseAbscissa W) W.rectangle.T u ≤
        (Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3) * (-δ) :=
    mul_le_mul_of_nonneg_left (hcore u hu) hprefPos
  have hmul₂ :
      (Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3) * (-δ) ≤
        cfzp025CenteredDerivativePrefactorFloor ε W p j * (-δ) :=
    mul_le_mul_of_nonpos_right hfloor (neg_nonpos.mpr hδ)
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv huPos.ne']
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 *
          cfzpNegativeFrequencyBoundaryProfileDerivativeCore
            (cfzpModePhaseAbscissa W) W.rectangle.T u ≤
        Real.exp (-(cfzpModePhaseAbscissa W) * u) / u ^ 3 * (-δ) := hmul₁
    _ ≤ cfzp025CenteredDerivativePrefactorFloor ε W p j * (-δ) := hmul₂
    _ = -(cfzp025CenteredDerivativePrefactorFloor ε W p j * δ) := by ring

/-! ## Gate E: event and pulse credit -/

/-- Phase-core margin gives the CFZP-023 quantitative event credit. -/
theorem cfzp025PrimePowerBranchFreeTrigEvent_ge_phaseCoreCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hphase : Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j * δ) ≤
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hκ : 0 ≤ cfzp025CenteredDerivativePrefactorFloor ε W p j * δ :=
    mul_nonneg (cfzp025CenteredDerivativePrefactorFloor_pos
      hε hε2 W hp hj).le hδ
  exact cfzp023PrimePowerBranchFreeTrigEvent_ge_quantitativeCredit
    hε hε2 W hp hj hκ
    (cfzp025CenteredProfileDerivativeDropMargin_of_phaseCoreMargin
      hε hε2 W hp hj hδ hphase)

/-- The same phase-core credit transports to the prime-power pulse. -/
theorem cfzp025VonMangoldtPulse_ge_phaseCoreCredit_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hphase : Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j * δ) ≤
      cfzp021VonMangoldtPulse ε W n := by
  rw [hn, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzp025PrimePowerBranchFreeTrigEvent_ge_phaseCoreCredit
    hε hε2 W hp hj hδ hphase

/-! ## Gate F: quantitative third-quadrant algebra -/

/-- Quantitative third-quadrant bounds force a negative phase derivative core. -/
theorem cfzp025PhaseDerivativeCore_le_neg_of_quantitativeThirdQuadrantCell
    {α θ A₀ B₀ s c : ℝ}
    (hA₀ : 0 ≤ A₀)
    (hA₀A : A₀ ≤ cfzpPhaseDerivativeSinCoeff α θ)
    (hs : 0 ≤ s)
    (hsin : Real.sin θ ≤ -s)
    (hB₀ : 0 ≤ B₀)
    (hB₀B : B₀ ≤ 2 * θ * (α * θ + 1))
    (hc : 0 ≤ c)
    (hcos : Real.cos θ ≤ -c) :
    cfzpPhaseDerivativeCore α θ ≤ -(A₀ * s + B₀ * c) := by
  have hA : 0 ≤ cfzpPhaseDerivativeSinCoeff α θ :=
    hA₀.trans hA₀A
  have hB : 0 ≤ 2 * θ * (α * θ + 1) :=
    hB₀.trans hB₀B
  have hsinTerm :
      cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ ≤ -(A₀ * s) := by
    calc
      cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ ≤
          cfzpPhaseDerivativeSinCoeff α θ * (-s) :=
        mul_le_mul_of_nonneg_left hsin hA
      _ ≤ A₀ * (-s) :=
        mul_le_mul_of_nonpos_right hA₀A (neg_nonpos.mpr hs)
      _ = -(A₀ * s) := by ring
  have hcosTerm :
      (2 * θ * (α * θ + 1)) * Real.cos θ ≤ -(B₀ * c) := by
    calc
      (2 * θ * (α * θ + 1)) * Real.cos θ ≤
          (2 * θ * (α * θ + 1)) * (-c) :=
        mul_le_mul_of_nonneg_left hcos hB
      _ ≤ B₀ * (-c) :=
        mul_le_mul_of_nonpos_right hB₀B (neg_nonpos.mpr hc)
      _ = -(B₀ * c) := by ring
  calc
    cfzpPhaseDerivativeCore α θ =
        cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ +
          (2 * θ * (α * θ + 1)) * Real.cos θ := by
      rfl
    _ ≤ -(A₀ * s) + -(B₀ * c) := add_le_add hsinTerm hcosTerm
    _ = -(A₀ * s + B₀ * c) := by ring

/-! ## Gate H: phase-core Good certificate constructor -/

/-- Build a CFZP-024 finite certificate from phase-core margins on `Good`.
The Bad-side envelope data remains an explicit CFZP-023 hypothesis. -/
noncomputable def cfzp025FiniteBlockCertificate_of_phaseCoreMargins
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (δ : ℕ × ℕ → ℝ)
    (hδ : ∀ pk ∈ Good, 0 ≤ δ pk)
    (hphase : ∀ pk ∈ Good,
      Cfzp025CenteredPhaseCoreNegativeMargin ε W pk.1 (pk.2 + 1) (δ pk))
    (K : ℕ × ℕ → ℝ)
    (hK : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good, 0 ≤ K pk)
    (henvelope : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
      Cfzp023CenteredProfileDerivativeAbsEnvelope ε W pk.1 (pk.2 + 1) (K pk)) :
    Cfzp024FiniteBlockCertificate ε W A B := by
  refine
    { Good := Good
      hGood := hGood
      κ := fun pk => cfzp025CenteredDerivativePrefactorFloor
        ε W pk.1 (pk.2 + 1) * δ pk
      K := K
      hκ := ?_
      hmargin := ?_
      hK := hK
      henvelope := henvelope }
  · intro pk hpk
    exact mul_nonneg
      (cfzp025CenteredDerivativePrefactorFloor_pos hε hε2 W
        (cfzp025_prime_and_positive_exponent hAB (hGood hpk)).1
        (cfzp025_prime_and_positive_exponent hAB (hGood hpk)).2).le
      (hδ pk hpk)
  · intro pk hpk
    exact cfzp025CenteredProfileDerivativeDropMargin_of_phaseCoreMargin
      hε hε2 W
      (cfzp025_prime_and_positive_exponent hAB (hGood hpk)).1
      (cfzp025_prime_and_positive_exponent hAB (hGood hpk)).2
      (hδ pk hpk) (hphase pk hpk)

/-! ## Gate J: provider firewall -/

/-- No independent quantitative phase-cell coverage provider is introduced. -/
inductive Cfzp025QuantitativePhaseCoreMarginSynthesisGap : Prop
  | noIndependentQuantitativePrimePowerPhaseCellCoverageProvider

end DkMath.RH.CFBRCProjection
