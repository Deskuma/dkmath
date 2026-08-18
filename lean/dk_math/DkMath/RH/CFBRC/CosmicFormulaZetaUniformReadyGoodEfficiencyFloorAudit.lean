/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaUniversalEnvelopeEfficiencyLedgerAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaUniformReadyGoodEfficiencyFloorAudit"

/-!
# CFZP-032: uniform ready-Good efficiency floors and weighted coverage

This module adds the finite normalization layer between the CFZP-031
efficiency ledger and a weighted reference-mass coverage criterion.  The
phase and prefactor ratios are separated, their common quadratic coefficient
is recorded, and an explicit large-cell contract gives a prime-independent
positive efficiency floor.

The large-cell contract is closed internally at the explicit thresholds
`k ≥ 1` and `j ≥ 3`.  This is a finite algebraic threshold, not an
equidistribution theorem.  Cofinal hits remain conditional on the existing
providers, while positive density, infinite sums, limit exchange, and RH
remain outside this module.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set
open DkMath.NumberTheory

private theorem cfzp032BadLocalShape_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp030BadLocalShape ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hright : 0 < cfzpPrimePowerPhaseAngleRight ε W p j := by
    rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
    exact mul_pos W.rectangle.hT hmag.2
  have hceiling : 0 < cfzp029CenteredDerivativePrefactorCeiling ε W p j :=
    cfzp029CenteredDerivativePrefactorCeiling_pos hε hε2 W hp hj
  have hcore : 0 < cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j) := by
    have hα : 0 < cfzpModePhaseAspectRatio W := cfzpModePhaseAspectRatio_pos W
    have hright : 0 < cfzpPrimePowerPhaseAngleRight ε W p j := by
      rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
      exact mul_pos W.rectangle.hT hmag.2
    have hsum : 0 < cfzpModePhaseAspectRatio W *
        cfzpPrimePowerPhaseAngleRight ε W p j + 1 := by
      nlinarith [mul_nonneg hα.le hright.le]
    have hmiddle : 0 < 2 *
        (cfzpModePhaseAspectRatio W *
          cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by
      nlinarith
    unfold cfzp029PhaseDerivativeCoreAbsEnvelope
    have hfirst : 0 ≤
        (cfzpPrimePowerPhaseAngleRight ε W p j) ^ 2 *
          |1 - (cfzpModePhaseAspectRatio W) ^ 2| := by positivity
    have hlast : 0 ≤ 2 * cfzpPrimePowerPhaseAngleRight ε W p j *
        (cfzpModePhaseAspectRatio W *
          cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by positivity
    linarith
  unfold cfzp030BadLocalShape cfzp029CenteredProfileDerivativeAbsBound
  exact mul_pos hceiling hcore

private theorem cfzp032_prime_and_positive_exponent
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

/-! ## Gate A: direct finite endpoint adapter -/

private noncomputable def cfzp032CanonicalCertificate
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
    Cfzp024FiniteBlockCertificate ε W A B :=
  cfzp029FiniteBlockCertificate_of_subcriticalReadyHits
    hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready

private theorem cfzp032CanonicalCertificate_badEnvelope_eq
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
    cfzp024CertifiedBadDebtEnvelope
        (cfzp024BadPrimePowerPairBlockSupport A B Good)
        (cfzp032CanonicalCertificate hε hε2 W hAB Good hGood k τ
          hsub hτ hτ4 hready).K =
      cfzp029AutomaticBadDebtEnvelope ε W
        (cfzp024BadPrimePowerPairBlockSupport A B Good) := by
  rfl

private theorem cfzp032CanonicalCertificate_netBalance_eq_ledger
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
    cfzp030CertifiedNetBalance W
        (cfzp032CanonicalCertificate hε hε2 W hAB Good hGood k τ
          hsub hτ hτ4 hready) =
      cfzp031EfficiencyLedger ε W A B Good k τ := by
  change
    cfzp024CertifiedGoodCredit Good
        (fun pk => cfzp030ReadyGoodShape ε W pk.1 (pk.2 + 1)
          (k pk) (τ pk)) -
      cfzp029AutomaticBadDebtEnvelope ε W
        (cfzp024BadPrimePowerPairBlockSupport A B Good) =
    cfzp031EfficiencyLedger ε W A B Good k τ
  rw [cfzp031EfficiencyLedger_eq_localCredit_sub_automaticBadDebt
    hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready]
  unfold cfzp024CertifiedGoodCredit
  congr 1

/-!
The public adapter below is the completion point of Gate A.  Its proof is
kept separate from the certificate construction so that later callers only
see ready-hit data and the ledger inequality.
-/

theorem cfzp032EfficiencyLedger_bound_implies_radialContactDeficit_le
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
        pk.1 (pk.2 + 1) (k pk) (τ pk))
    {η : ℝ}
    (hledger :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
        cfzp031EfficiencyLedger ε W A B Good k τ + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  let cert := cfzp032CanonicalCertificate hε hε2 W hAB Good hGood k τ
    hsub hτ hτ4 hready
  have hnet : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp030CertifiedNetBalance W cert + η := by
    rw [cfzp032CanonicalCertificate_netBalance_eq_ledger
      hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready]
    exact hledger
  exact cfzp030NetBalance_bound_implies_radialContactDeficit_le
    hε hε2 W hAB cert
    (cfzp032CanonicalCertificate_badEnvelope_eq
      hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready)
    hnet

/-! ## Gate B: phase efficiency factorization -/

/-- The Good phase margin divided by the universal Bad phase envelope. -/
noncomputable def cfzp032ReadyGoodPhaseEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : ℝ :=
  cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ /
    cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j)

/-- The Good efficiency is the product of prefactor and phase efficiencies. -/
theorem cfzp031ReadyGoodEfficiency_eq_prefactor_mul_phase
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (_hsub : Cfzp027SubcriticalPhaseAspect W) (_hτ : 0 < τ)
    (_hτ4 : τ ≤ Real.pi / 4)
    (_hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    cfzp031ReadyGoodEfficiency ε W p j k τ =
      cfzp031PrefactorEfficiency ε W p j *
        cfzp032ReadyGoodPhaseEfficiency ε W p j k τ := by
  have hbad := cfzp032BadLocalShape_pos hε hε2 W hp hj
  have hceiling := cfzp029CenteredDerivativePrefactorCeiling_pos hε hε2 W hp hj
  have hcore : 0 < cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j) := by
    have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
      hε hε2 hp hj
    have hright : 0 < cfzpPrimePowerPhaseAngleRight ε W p j := by
      rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
      exact mul_pos W.rectangle.hT hmag.2
    have hα : 0 < cfzpModePhaseAspectRatio W := cfzpModePhaseAspectRatio_pos W
    have hsum : 0 < cfzpModePhaseAspectRatio W *
        cfzpPrimePowerPhaseAngleRight ε W p j + 1 := by
      nlinarith [mul_nonneg hα.le hright.le]
    have hmiddle : 0 < 2 *
        (cfzpModePhaseAspectRatio W *
          cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by nlinarith
    unfold cfzp029PhaseDerivativeCoreAbsEnvelope
    have hfirst : 0 ≤
        (cfzpPrimePowerPhaseAngleRight ε W p j) ^ 2 *
          |1 - (cfzpModePhaseAspectRatio W) ^ 2| := by positivity
    have hlast : 0 ≤ 2 * cfzpPrimePowerPhaseAngleRight ε W p j *
        (cfzpModePhaseAspectRatio W *
          cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by positivity
    linarith
  unfold cfzp031ReadyGoodEfficiency cfzp032ReadyGoodPhaseEfficiency
    cfzp030ReadyGoodShape cfzp030BadLocalShape
  rw [cfzp025CenteredDerivativePrefactorFloor_eq_efficiency_mul_cfzp029Ceiling
    hε hε2 W hp hj]
  rw [show cfzp029CenteredProfileDerivativeAbsBound ε W p j =
      cfzp029CenteredDerivativePrefactorCeiling ε W p j *
        cfzp029PhaseDerivativeCoreAbsEnvelope
          (cfzpModePhaseAspectRatio W)
          (cfzpPrimePowerPhaseAngleRight ε W p j) by rfl]
  field_simp [ne_of_gt hbad, ne_of_gt hcore, ne_of_gt hceiling]

/-- The phase efficiency is positive for a subcritical ready hit. -/
theorem cfzp032ReadyGoodPhaseEfficiency_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    0 < cfzp032ReadyGoodPhaseEfficiency ε W p j k τ := by
  unfold cfzp032ReadyGoodPhaseEfficiency
  exact div_pos
    (cfzp027PhaseCoreMargin_pos_of_subcritical_ready_hit
      W hsub hτ hτ4 hhit)
    (by
      have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
        hε hε2 hp hj
      have hright : 0 < cfzpPrimePowerPhaseAngleRight ε W p j := by
        rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
        exact mul_pos W.rectangle.hT hmag.2
      have hα : 0 < cfzpModePhaseAspectRatio W := cfzpModePhaseAspectRatio_pos W
      have hsum : 0 < cfzpModePhaseAspectRatio W *
          cfzpPrimePowerPhaseAngleRight ε W p j + 1 := by
        nlinarith [mul_nonneg hα.le hright.le]
      have hmiddle : 0 < 2 *
          (cfzpModePhaseAspectRatio W *
            cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by
        nlinarith
      unfold cfzp029PhaseDerivativeCoreAbsEnvelope
      have hfirst : 0 ≤
          (cfzpPrimePowerPhaseAngleRight ε W p j) ^ 2 *
            |1 - (cfzpModePhaseAspectRatio W) ^ 2| := by positivity
      have hlast : 0 ≤ 2 * cfzpPrimePowerPhaseAngleRight ε W p j *
          (cfzpModePhaseAspectRatio W *
            cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by positivity
      linarith)

/-- The phase denominator is positive on every safe prime-power cell. -/
theorem cfzp032PhaseEnvelope_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hright : 0 < cfzpPrimePowerPhaseAngleRight ε W p j := by
    rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
    exact mul_pos W.rectangle.hT hmag.2
  have hα : 0 < cfzpModePhaseAspectRatio W := cfzpModePhaseAspectRatio_pos W
  have hsum : 0 < cfzpModePhaseAspectRatio W *
      cfzpPrimePowerPhaseAngleRight ε W p j + 1 := by
    nlinarith [mul_nonneg hα.le hright.le]
  have hmiddle : 0 < 2 *
      (cfzpModePhaseAspectRatio W *
        cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by
    nlinarith
  unfold cfzp029PhaseDerivativeCoreAbsEnvelope
  have hfirst : 0 ≤
      (cfzpPrimePowerPhaseAngleRight ε W p j) ^ 2 *
        |1 - (cfzpModePhaseAspectRatio W) ^ 2| := by positivity
  have hlast : 0 ≤ 2 * cfzpPrimePowerPhaseAngleRight ε W p j *
      (cfzpModePhaseAspectRatio W *
        cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by positivity
  linarith

/-! ## Gate C: monotonicity of the phase envelope -/

/-- The universal phase envelope is monotone in its right endpoint. -/
theorem cfzp029PhaseDerivativeCoreAbsEnvelope_mono_right
    {α R₁ R₂ : ℝ} (hα : 0 ≤ α) (hR₁ : 0 ≤ R₁)
    (hR : R₁ ≤ R₂) :
    cfzp029PhaseDerivativeCoreAbsEnvelope α R₁ ≤
      cfzp029PhaseDerivativeCoreAbsEnvelope α R₂ := by
  unfold cfzp029PhaseDerivativeCoreAbsEnvelope
  have hsquares : R₁ ^ 2 ≤ R₂ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (add_nonneg hR₁ (le_trans hR₁ hR))]
  have hlin : α * R₁ + 1 ≤ α * R₂ + 1 := by
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left hR hα) 1
  have hfirst : R₁ ^ 2 * |1 - α ^ 2| ≤ R₂ ^ 2 * |1 - α ^ 2| :=
    mul_le_mul_of_nonneg_right hsquares (abs_nonneg _)
  have hsecond : 2 * (α * R₁ + 1) ≤ 2 * (α * R₂ + 1) := by
    exact mul_le_mul_of_nonneg_left hlin (by norm_num)
  have hthird : 2 * R₁ * (α * R₁ + 1) ≤
      2 * R₂ * (α * R₂ + 1) := by
    have hR₂ : 0 ≤ R₂ := le_trans hR₁ hR
    calc
      2 * R₁ * (α * R₁ + 1) ≤
          2 * R₂ * (α * R₁ + 1) := by
        nlinarith [mul_le_mul_of_nonneg_right hR
          (show 0 ≤ 2 * (α * R₁ + 1) by positivity)]
      _ ≤ 2 * R₂ * (α * R₂ + 1) := by
        nlinarith [mul_le_mul_of_nonneg_left hlin
          (show 0 ≤ 2 * R₂ by positivity)]
  nlinarith

/-! ## Gate D: common quadratic coefficient -/

/-- The common subcritical quadratic coefficient. -/
noncomputable def cfzp032SubcriticalQuadraticCoefficient (α : ℝ) : ℝ :=
  1 + 2 * α - α ^ 2

/-- In the subcritical range the quadratic coefficient is at least one. -/
theorem cfzp032SubcriticalQuadraticCoefficient_ge_one
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    1 ≤ cfzp032SubcriticalQuadraticCoefficient α := by
  unfold cfzp032SubcriticalQuadraticCoefficient
  nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hα1.le)]

/-- The quadratic coefficient is strictly positive in the subcritical range. -/
theorem cfzp032SubcriticalQuadraticCoefficient_pos
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < cfzp032SubcriticalQuadraticCoefficient α :=
  lt_of_lt_of_le (by norm_num) (cfzp032SubcriticalQuadraticCoefficient_ge_one hα0 hα1)

/-- The absolute-value coefficient has its subcritical normal form. -/
theorem cfzp032_abs_one_sub_sq_eq
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    |1 - α ^ 2| = 1 - α ^ 2 := by
  rw [abs_of_nonneg]
  nlinarith [mul_nonneg (sub_nonneg.mpr hα1.le) (add_nonneg hα0 (by linarith))]

/-- The Good coefficient floor has the common quadratic normal form. -/
theorem cfzp032PhaseMarginCoefficient_eq_quadratic
    {α L R : ℝ} :
    cfzp026PhaseSinCoeffFloor α L R +
        cfzp026PhaseCosCoeffFloor α L =
      cfzp032SubcriticalQuadraticCoefficient α * L ^ 2 +
        2 * L - 2 * α * R - 2 := by
  unfold cfzp026PhaseSinCoeffFloor cfzp026PhaseCosCoeffFloor
    cfzp032SubcriticalQuadraticCoefficient
  ring

/-- The Bad envelope has the same quadratic coefficient in the subcritical range. -/
theorem cfzp032PhaseEnvelope_eq_quadratic
    {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    cfzp029PhaseDerivativeCoreAbsEnvelope α R =
      cfzp032SubcriticalQuadraticCoefficient α * R ^ 2 +
        2 * (α + 1) * R + 2 := by
  unfold cfzp029PhaseDerivativeCoreAbsEnvelope
  rw [cfzp032_abs_one_sub_sq_eq hα0 hα1]
  unfold cfzp032SubcriticalQuadraticCoefficient
  ring

/-! ## Gate E/F: explicit finite uniform floor contract -/

/-- Explicit quadratic-vs-linear readiness for a trimmed phase cell. -/
def Cfzp032LargeCellEfficiencyReady (α : ℝ) (k : ℕ) (τ : ℝ) : Prop :=
  let L := cfzp026ThirdQuadrantCellLeft k τ
  let R := cfzp026ThirdQuadrantCellRight k τ
  let q := cfzp032SubcriticalQuadraticCoefficient α
  2 * (α * R + 1) ≤ q * L ^ 2 / 2 ∧
  2 * (α + 1) * R + 2 ≤ q * R ^ 2 ∧
  R ≤ 2 * L

/-- The large-cell contract is automatic once the periodic index is positive. -/
theorem cfzp032LargeCellEfficiencyReady_of_one_le
    {α τ : ℝ} {k : ℕ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hτ0 : 0 ≤ τ) (hτ4 : τ ≤ Real.pi / 4)
    (hk : 1 ≤ k) :
    Cfzp032LargeCellEfficiencyReady α k τ := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hα1' : α ≤ 1 := hα1.le
  have hL : 9 < cfzp026ThirdQuadrantCellLeft k τ := by
    unfold cfzp026ThirdQuadrantCellLeft
    nlinarith [Real.pi_pos]
  have hR : 9 < cfzp026ThirdQuadrantCellRight k τ := by
    unfold cfzp026ThirdQuadrantCellRight
    nlinarith [Real.pi_pos]
  have hLR : cfzp026ThirdQuadrantCellRight k τ ≤
      2 * cfzp026ThirdQuadrantCellLeft k τ := by
    unfold cfzp026ThirdQuadrantCellRight cfzp026ThirdQuadrantCellLeft
    nlinarith [Real.pi_pos]
  have hq : 1 ≤ cfzp032SubcriticalQuadraticCoefficient α :=
    cfzp032SubcriticalQuadraticCoefficient_ge_one hα0 hα1
  refine ⟨?_, ?_, hLR⟩
  · nlinarith [sq_nonneg (cfzp026ThirdQuadrantCellLeft k τ)]
  · nlinarith [sq_nonneg (cfzp026ThirdQuadrantCellRight k τ)]

/-- The prefactor-left threshold is automatic for prime powers with `j ≥ 3`. -/
theorem cfzp032_two_epsilon_le_phaseMagnitudeLeft_of_three_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 3 ≤ j) :
    2 * ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p j := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · change (0 : ℝ) < (p : ℝ)
      exact_mod_cast hp.pos
    · exact hp2r
  unfold cfzpPrimePowerPhaseMagnitudeLeft cfzpPrimePowerPhaseCenter
  have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- A finite contract combining cell size and the prefactor containment. -/
def Cfzp032UniformReadyCell
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : Prop :=
  Cfzp032LargeCellEfficiencyReady
    (cfzpModePhaseAspectRatio W) k τ ∧
  2 * ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p j

/-- Both components of `UniformReadyCell` follow from explicit large indices. -/
theorem cfzp032UniformReadyCell_of_large_indices
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ}
    (hp : Nat.Prime p)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hj : 3 ≤ j) (hk : 1 ≤ k) :
    Cfzp032UniformReadyCell ε W p j k τ := by
  refine ⟨?_, ?_⟩
  · exact cfzp032LargeCellEfficiencyReady_of_one_le
      (cfzpModePhaseAspectRatio_pos W).le hsub hτ.le hτ4 hk
  · exact cfzp032_two_epsilon_le_phaseMagnitudeLeft_of_three_le
      hε hε2 hp hj

/-- A large-cell phase contract gives the explicit `sin τ / 16` floor. -/
theorem cfzp032PhaseEfficiency_ge_sin_div_16
    {α L R τ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hL : 0 < L) (hR : 0 < R) (hτ : 0 ≤ Real.sin τ)
    (hready :
      2 * (α * R + 1) ≤
          cfzp032SubcriticalQuadraticCoefficient α * L ^ 2 / 2 ∧
      2 * (α + 1) * R + 2 ≤
          cfzp032SubcriticalQuadraticCoefficient α * R ^ 2 ∧
      R ≤ 2 * L) :
    Real.sin τ / 16 ≤
      (cfzp032SubcriticalQuadraticCoefficient α * L ^ 2 +
          2 * L - 2 * α * R - 2) * Real.sin τ /
        cfzp029PhaseDerivativeCoreAbsEnvelope α R := by
  have hq : 1 ≤ cfzp032SubcriticalQuadraticCoefficient α :=
    cfzp032SubcriticalQuadraticCoefficient_ge_one hα0 hα1
  have hq0 : 0 < cfzp032SubcriticalQuadraticCoefficient α :=
    (cfzp032SubcriticalQuadraticCoefficient_pos hα0 hα1)
  have hnum :
      L ^ 2 / 2 ≤ cfzp032SubcriticalQuadraticCoefficient α * L ^ 2 +
          2 * L - 2 * α * R - 2 := by
    nlinarith [sq_nonneg L]
  have hden : cfzp029PhaseDerivativeCoreAbsEnvelope α R ≤
      2 * cfzp032SubcriticalQuadraticCoefficient α * R ^ 2 := by
    rw [cfzp032PhaseEnvelope_eq_quadratic hα0 hα1]
    nlinarith [sq_nonneg R]
  have hR2 : R ^ 2 ≤ 4 * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hready.2.2) (add_nonneg hR.le (by positivity))]
  have hdenpos : 0 < cfzp029PhaseDerivativeCoreAbsEnvelope α R := by
    rw [cfzp032PhaseEnvelope_eq_quadratic hα0 hα1]
    positivity
  apply (le_div_iff₀ hdenpos).2
  have hmul :
      cfzp032SubcriticalQuadraticCoefficient α * R ^ 2 * Real.sin τ ≤
        4 * cfzp032SubcriticalQuadraticCoefficient α * L ^ 2 * Real.sin τ := by
    have hquad :
        cfzp032SubcriticalQuadraticCoefficient α * R ^ 2 ≤
          4 * cfzp032SubcriticalQuadraticCoefficient α * L ^ 2 := by
      have hqmul := mul_le_mul_of_nonneg_left hR2
        (cfzp032SubcriticalQuadraticCoefficient_pos hα0 hα1).le
      nlinarith [hqmul]
    exact mul_le_mul_of_nonneg_right hquad hτ
  nlinarith [hnum, hden, hmul]

/-- The prefactor ratio has the uniform lower bound `exp(-2aε)/8`. -/
theorem cfzp031PrefactorEfficiency_ge_exp_div_eight
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hleft : 2 * ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p j) :
    Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) / 8 ≤
      cfzp031PrefactorEfficiency ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hratio : (1 / 2 : ℝ) ≤
      cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j := by
    apply (le_div_iff₀ hmag.2).2
    have hw := cfzp023PrimePowerPhaseMagnitude_width ε p j
    nlinarith [hleft, hw]
  have hexp : Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) ≤
      Real.exp (-(cfzpModePhaseAbscissa W) *
        (cfzpPrimePowerPhaseMagnitudeRight ε p j -
          cfzpPrimePowerPhaseMagnitudeLeft ε p j)) := by
    apply Real.exp_le_exp.mpr
    have ha := (cfzpModePhaseAbscissa_pos W).le
    rw [cfzp023PrimePowerPhaseMagnitude_width ε p j]
  unfold cfzp031PrefactorEfficiency
  dsimp
  have hpow : (1 / 2 : ℝ) ^ 3 ≤
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hratio 3
  have hpow' : (1 / 8 : ℝ) ≤
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
    norm_num at hpow ⊢
    exact hpow
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) / 8 ≤
        Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) *
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
            cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
      calc
        Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) / 8 =
            Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) * (1 / 8) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow' (Real.exp_pos _).le
    _ ≤ cfzp031PrefactorEfficiency ε W p j := by
      unfold cfzp031PrefactorEfficiency
      dsimp
      exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- The explicit positive floor used by the uniform Good efficiency theorem. -/
noncomputable def cfzp032UniformReadyGoodEfficiencyFloor
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) : ℝ :=
  Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) * Real.sin τ / 128

/-- The uniform floor is positive for a strictly trimmed target. -/
theorem cfzp032UniformReadyGoodEfficiencyFloor_pos
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {τ : ℝ}
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4) :
    0 < cfzp032UniformReadyGoodEfficiencyFloor ε W τ := by
  unfold cfzp032UniformReadyGoodEfficiencyFloor
  have hs : 0 < Real.sin τ :=
    Real.sin_pos_of_pos_of_lt_pi hτ (by nlinarith [hτ4, Real.pi_pos])
  positivity

/-! ## Gate G/H: conditional uniform-hit transport -/

/-- A ready hit satisfying the finite large-cell contract has uniform efficiency. -/
theorem cfzp032UniformReadyGoodEfficiencyFloor_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ)
    (hj : 3 ≤ j) (hk : 1 ≤ k) :
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
      cfzp031ReadyGoodEfficiency ε W p j k τ := by
  have hlarge := cfzp032UniformReadyCell_of_large_indices
    hε hε2 W hp hsub hτ hτ4 hj hk
  have hjpos : 0 < j := by omega
  have hphase := hlarge.1
  change
    2 * (cfzpModePhaseAspectRatio W *
        cfzp026ThirdQuadrantCellRight k τ + 1) ≤
        cfzp032SubcriticalQuadraticCoefficient (cfzpModePhaseAspectRatio W) *
          cfzp026ThirdQuadrantCellLeft k τ ^ 2 / 2 ∧
      2 * (cfzpModePhaseAspectRatio W + 1) *
          cfzp026ThirdQuadrantCellRight k τ + 2 ≤
        cfzp032SubcriticalQuadraticCoefficient (cfzpModePhaseAspectRatio W) *
          cfzp026ThirdQuadrantCellRight k τ ^ 2 ∧
      cfzp026ThirdQuadrantCellRight k τ ≤
        2 * cfzp026ThirdQuadrantCellLeft k τ at hphase
  have hL := cfzp026ThirdQuadrantCellLeft_pos (k := k) hτ.le
  have hR : 0 < cfzp026ThirdQuadrantCellRight k τ := by
    have hLR := cfzp026ThirdQuadrantCellLeft_le_right (k := k) (τ := τ) hτ4
    exact lt_of_lt_of_le hL hLR
  have hsin : 0 ≤ Real.sin τ :=
    (Real.sin_pos_of_pos_of_lt_pi hτ (by nlinarith [hτ4, Real.pi_pos])).le
  have hratio := cfzp032PhaseEfficiency_ge_sin_div_16
    (cfzpModePhaseAspectRatio_pos W).le hsub hL hR hsin hphase
  have hpref := cfzp031PrefactorEfficiency_ge_exp_div_eight hε hε2 W hp hjpos
    hlarge.2
  have hfac := cfzp031ReadyGoodEfficiency_eq_prefactor_mul_phase
    hε hε2 W hp hjpos hsub hτ hτ4 hhit
  have hphaseActual :
      cfzp032ReadyGoodPhaseEfficiency ε W p j k τ ≥ Real.sin τ / 16 := by
    unfold cfzp032ReadyGoodPhaseEfficiency
    have hcontain := cfzp027_containment_of_ready_hit hhit
    have hangle := hcontain.2
    have hright := hangle
    have hRactual : 0 ≤ cfzpPrimePowerPhaseAngleRight ε W p j := by
      have hm := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
        hε hε2 hp hjpos
      rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
      exact (mul_pos W.rectangle.hT hm.2).le
    have hmono := cfzp029PhaseDerivativeCoreAbsEnvelope_mono_right
      (cfzpModePhaseAspectRatio_pos W).le hRactual hright
    have hcell : Real.sin τ / 16 ≤
        cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ /
          cfzp029PhaseDerivativeCoreAbsEnvelope
            (cfzpModePhaseAspectRatio W)
            (cfzp026ThirdQuadrantCellRight k τ) := by
      simpa only [cfzp026PhaseCoreMargin,
        cfzp032PhaseMarginCoefficient_eq_quadratic] using hratio
    exact le_trans hcell (by
      apply div_le_div_of_nonneg_left
      · exact (cfzp027PhaseCoreMargin_pos_of_subcritical_ready_hit
          W hsub hτ hτ4 hhit).le
      · exact (cfzp032PhaseEnvelope_pos hε hε2 W hp hjpos)
      · exact hmono)
  unfold cfzp032UniformReadyGoodEfficiencyFloor
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) * Real.sin τ / 128 =
        (Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) / 8) *
          (Real.sin τ / 16) := by ring
    _ ≤ cfzp031PrefactorEfficiency ε W p j *
          cfzp032ReadyGoodPhaseEfficiency ε W p j k τ := by
      have hsin16 : 0 ≤ Real.sin τ / 16 := by positivity
      have hpref0 : 0 ≤ cfzp031PrefactorEfficiency ε W p j :=
        (cfzp031PrefactorEfficiency_pos hε hε2 W hp hjpos).le
      exact mul_le_mul hpref hphaseActual hsin16 hpref0
    _ = cfzp031ReadyGoodEfficiency ε W p j k τ := hfac.symm

/-- Cofinal ready hits become uniformly efficient once the finite thresholds are supplied. -/
theorem cfzp032_exists_uniformly_efficient_ready_hit_of_cofinal
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ} {τ : ℝ}
    (hp : Nat.Prime p) (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hcofinal : Cfzp027CofinalReadyThirdQuadrantHitsForPrime ε W p τ) :
    ∀ J K : ℕ, ∃ j k : ℕ,
      J ≤ j ∧ K ≤ k ∧
        Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ ∧
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
          cfzp031ReadyGoodEfficiency ε W p j k τ := by
  intro J K
  obtain ⟨j, k, hj, hk, hhit⟩ := hcofinal (max J 3) (max K 1)
  have hjpos : 0 < j := by omega
  have hj3 : 3 ≤ j := le_trans (le_max_right J 3) hj
  have hk1 : 1 ≤ k := le_trans (le_max_right K 1) hk
  refine ⟨j, k, le_trans (le_max_left J 3) hj,
    le_trans (le_max_left K 1) hk, hhit, ?_⟩
  exact cfzp032UniformReadyGoodEfficiencyFloor_le hε hε2 W hp hjpos
    hsub hτ hτ4 hhit hj3 hk1

/-- The irrational-rotation adapter supplies the cofinal provider directly. -/
theorem cfzp032_exists_uniformly_efficient_ready_hit_of_irrationalRotation
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ} {τ : ℝ}
    (hp : Nat.Prime p) (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ)
    (hirr : Cfzp028PrimePhaseRotationIrrational W p) :
    ∀ J K : ℕ, ∃ j k : ℕ,
      J ≤ j ∧ K ≤ k ∧
        Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ ∧
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
          cfzp031ReadyGoodEfficiency ε W p j k τ := by
  apply cfzp032_exists_uniformly_efficient_ready_hit_of_cofinal
    hε hε2 W hp hsub hτ hτ4
  exact cfzp028CofinalReadyThirdQuadrantHitsForPrime_of_irrationalRotation
    W hp hε hτ hτ4 hsub hinterior hirr

/-! ## Gate I: weighted reference-mass coverage -/

/-- Total reference mass of a finite block. -/
noncomputable def cfzp032BlockReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)

/-- Reference mass captured by a chosen Good subset. -/
noncomputable def cfzp032GoodReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (Good : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ Good,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)

/-- Reference mass is nonnegative on a canonical safe block. -/
theorem cfzp032PrimePowerReferenceMass_nonneg
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    0 ≤ cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact (cfzp031PrimePowerReferenceMass_pos hε hε2 W
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1 (by omega)).le

/-- Block mass splits exactly into Good and complementary Bad mass. -/
theorem cfzp032BlockReferenceMass_eq_good_add_bad
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (_hAB : A ≤ B) (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B) :
    cfzp032BlockReferenceMass ε W A B =
      cfzp032GoodReferenceMass ε W Good +
        ∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
          cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) := by
  have hunion := cfzp024GoodUnionBad_eq_block Good hGood
  unfold cfzp032BlockReferenceMass cfzp032GoodReferenceMass
  rw [← hunion, Finset.sum_union (cfzp024GoodDisjointBad Good)]

/-- The efficiency ledger dominates the floor-weighted Good mass deficit. -/
theorem cfzp032_floor_good_mass_sub_block_mass_le_ledger
    {ε ρ : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hfloor : ∀ pk ∈ Good, ρ ≤
      cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk)) :
    (1 + ρ) * cfzp032GoodReferenceMass ε W Good -
        cfzp032BlockReferenceMass ε W A B ≤
      cfzp031EfficiencyLedger ε W A B Good k τ := by
  have hsplit := cfzp032BlockReferenceMass_eq_good_add_bad
    ε W hAB Good hGood
  rw [hsplit]
  unfold cfzp031EfficiencyLedger cfzp032GoodReferenceMass
  have hmass : ∀ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
      0 ≤ cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) :=
    fun pk hpk => cfzp032PrimePowerReferenceMass_nonneg hε hε2 W hAB hpk
  have hgood :
      (∑ pk ∈ Good, ρ * cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) ≤
        ∑ pk ∈ Good,
          cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk) *
            cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) := by
    apply Finset.sum_le_sum
    intro pk hpk
    exact mul_le_mul_of_nonneg_right (hfloor pk hpk)
      (hmass pk (hGood hpk))
  rw [Finset.mul_sum]
  have hsum₁ :
      (∑ pk ∈ Good, (1 + ρ) *
        cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) =
      (∑ pk ∈ Good, cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) +
        ∑ pk ∈ Good, ρ * cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pk hpk
    ring
  rw [hsum₁]
  nlinarith [hgood]

/-- A finite weighted coverage inequality reaches the radial endpoint. -/
theorem cfzp032_weightedCoverage_implies_radialContactDeficit_le
    {ε ρ η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk))
    (hfloor : ∀ pk ∈ Good, ρ ≤
      cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk))
    (hcoverage :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp032BlockReferenceMass ε W A B ≤
        (1 + ρ) * cfzp032GoodReferenceMass ε W Good + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  apply cfzp032EfficiencyLedger_bound_implies_radialContactDeficit_le
    hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready
  have hledger := cfzp032_floor_good_mass_sub_block_mass_le_ledger
    hε hε2 W hAB Good hGood k τ hfloor
  nlinarith

/-! ## Firewall -/

/-- Remaining weighted-density and arithmetic providers are explicit gaps. -/
inductive Cfzp032UniformReadyGoodEfficiencyFloorGap : Prop
  | noIndependentWeightedReferenceMassCoverageProvider
  | noPositiveWeightedDensityProvider
  | noPrimeAxisWeightedMassProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider

end DkMath.RH.CFBRCProjection
