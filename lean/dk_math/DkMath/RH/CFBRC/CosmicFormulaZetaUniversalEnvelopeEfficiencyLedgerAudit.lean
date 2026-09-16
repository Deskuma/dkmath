/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaWeightedPrimePowerCreditDebtFactorizationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaUniversalEnvelopeEfficiencyLedgerAudit"

/-!
# CFZP-031: universal-envelope efficiency ledger

The automatic Bad envelope from CFZP-029 is used as a positive reference mass.
Ready Good hits are then measured by a dimensionless positive efficiency
coefficient.  The resulting finite ledger has Good contribution `+ρ * μ` and
Bad contribution `-μ`, and can also be written as one signed occupancy sum.

This is an exact finite normalization layer.  It does not assert weighted
occupancy dominance, positive weighted density, an infinite sum, a limit, or
RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory

/-! ## Gate A: universal reference mass -/

private theorem cfzp031BadLocalShape_pos
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
    have hα : 0 ≤ cfzpModePhaseAspectRatio W :=
      (cfzpModePhaseAspectRatio_pos W).le
    have hR : 0 ≤ cfzpPrimePowerPhaseAngleRight ε W p j := hright.le
    have hmiddle : 0 < 2 *
        (cfzpModePhaseAspectRatio W *
          cfzpPrimePowerPhaseAngleRight ε W p j + 1) := by
      positivity
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

/-- The canonical reference mass attached to a safe prime-power pair. -/
noncomputable def cfzp031PrimePowerReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp030PrimePowerCriticalCarrier p j *
    cfzp030BadLocalShape ε W p j

/-- The reference mass is exactly the CFZP-029 automatic Bad debt. -/
theorem cfzp031PrimePowerReferenceMass_eq_badDebtEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) :
    cfzp031PrimePowerReferenceMass ε W p j =
      cfzp029PrimePowerBadDebtEnvelope ε W p j := by
  unfold cfzp031PrimePowerReferenceMass
  exact (cfzp029PrimePowerBadDebtEnvelope_eq_carrier_mul_badShape
    ε W p j).symm

/-- The reference mass is strictly positive on every safe prime-power cell. -/
theorem cfzp031PrimePowerReferenceMass_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp031PrimePowerReferenceMass ε W p j := by
  exact mul_pos
    (cfzp030PrimePowerCriticalCarrier_pos hp hj)
    (cfzp031BadLocalShape_pos hε hε2 W hp hj)

/-! ## Gate B: ready Good efficiency -/

/-- The positive Good-shape coefficient relative to the Bad reference shape. -/
noncomputable def cfzp031ReadyGoodEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : ℝ :=
  cfzp030ReadyGoodShape ε W p j k τ /
    cfzp030BadLocalShape ε W p j

/-- A subcritical ready hit has strictly positive efficiency. -/
theorem cfzp031ReadyGoodEfficiency_pos_of_subcritical_ready_hit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    0 < cfzp031ReadyGoodEfficiency ε W p j k τ := by
  unfold cfzp031ReadyGoodEfficiency
  exact div_pos
    (cfzp030ReadyGoodShape_pos_of_subcritical_ready_hit
      hε hε2 W hp hj hsub hτ hτ4 hhit)
    (cfzp031BadLocalShape_pos hε hε2 W hp hj)

/-- The Good local credit is efficiency times the universal reference mass. -/
theorem cfzp030GoodLocalCredit_eq_efficiency_mul_referenceMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (_hsub : Cfzp027SubcriticalPhaseAspect W) (_hτ : 0 < τ)
    (_hτ4 : τ ≤ Real.pi / 4)
    (_hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    cfzp030GoodLocalCredit p j
        (cfzp030ReadyGoodShape ε W p j k τ) =
      cfzp031ReadyGoodEfficiency ε W p j k τ *
        cfzp031PrimePowerReferenceMass ε W p j := by
  have hbad := cfzp031BadLocalShape_pos hε hε2 W hp hj
  rw [cfzp030ReadyGoodLocalCredit_eq]
  unfold cfzp031ReadyGoodEfficiency cfzp031PrimePowerReferenceMass
    cfzp030ReadyGoodShape
  field_simp [ne_of_gt hbad]

/-! ## Gate C: exact prefactor efficiency -/

/-- The finite ratio between the Good floor and Bad ceiling prefactors. -/
noncomputable def cfzp031PrefactorEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  let l := cfzpPrimePowerPhaseMagnitudeLeft ε p j
  let r := cfzpPrimePowerPhaseMagnitudeRight ε p j
  Real.exp (-(cfzpModePhaseAbscissa W) * (r - l)) * (l / r) ^ 3

/-- The prefactor efficiency is positive on a safe prime-power cell. -/
theorem cfzp031PrefactorEfficiency_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp031PrefactorEfficiency ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hratio : 0 <
      cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j :=
    div_pos hmag.1 hmag.2
  unfold cfzp031PrefactorEfficiency
  dsimp
  exact mul_pos (Real.exp_pos _) (pow_pos hratio 3)

/-- The prefactor efficiency is at most one. -/
theorem cfzp031PrefactorEfficiency_le_one
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzp031PrefactorEfficiency ε W p j ≤ 1 := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hlt := cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j
  have ha : 0 ≤ cfzpModePhaseAbscissa W :=
    (cfzpModePhaseAbscissa_pos W).le
  have hgap : 0 ≤
      cfzpPrimePowerPhaseMagnitudeRight ε p j -
        cfzpPrimePowerPhaseMagnitudeLeft ε p j := sub_nonneg.mpr hlt.le
  have hexp : Real.exp (-(cfzpModePhaseAbscissa W) *
      (cfzpPrimePowerPhaseMagnitudeRight ε p j -
        cfzpPrimePowerPhaseMagnitudeLeft ε p j)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr ha) hgap
  have hratio0 : 0 ≤
      cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j :=
    (div_pos hmag.1 hmag.2).le
  have hratio1 :
      cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j ≤ 1 := by
    exact (div_le_iff₀ hmag.2).2 (by linarith)
  have hratio3 :
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
        cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hratio0 hratio1 3
  unfold cfzp031PrefactorEfficiency
  dsimp
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) *
        (cfzpPrimePowerPhaseMagnitudeRight ε p j -
          cfzpPrimePowerPhaseMagnitudeLeft ε p j)) *
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
          cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 ≤
      1 * (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
          cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hratio3 (by norm_num)
    _ = 1 := by ring

/-- Exact endpoint identity for the Good floor and Bad ceiling. -/
theorem cfzp025CenteredDerivativePrefactorFloor_eq_efficiency_mul_cfzp029Ceiling
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzp025CenteredDerivativePrefactorFloor ε W p j =
      cfzp031PrefactorEfficiency ε W p j *
        cfzp029CenteredDerivativePrefactorCeiling ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hl : cfzpPrimePowerPhaseMagnitudeLeft ε p j ≠ 0 :=
    ne_of_gt hmag.1
  have hr : cfzpPrimePowerPhaseMagnitudeRight ε p j ≠ 0 :=
    ne_of_gt hmag.2
  unfold cfzp025CenteredDerivativePrefactorFloor
    cfzp031PrefactorEfficiency cfzp029CenteredDerivativePrefactorCeiling
  dsimp
  field_simp [hl, hr]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Endpoint difference normal form for the prefactor efficiency. -/
theorem cfzp031PrefactorEfficiency_eq_width_form
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} :
    cfzp031PrefactorEfficiency ε W p j =
      Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) *
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j /
          cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
  unfold cfzp031PrefactorEfficiency
  dsimp
  rw [cfzp023PrimePowerPhaseMagnitude_width]

/-! ## Gate D: finite efficiency ledger -/

/-- The finite Good-minus-Bad efficiency ledger. -/
noncomputable def cfzp031EfficiencyLedger
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) (Good : Finset (ℕ × ℕ))
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ) : ℝ :=
  (∑ pk ∈ Good,
    cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk) *
      cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) -
  (∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1))

private theorem cfzp031_prime_and_positive_exponent
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

private theorem cfzp031_good_efficiency_sum_eq_local_credit_sum
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk)) :
    (∑ pk ∈ Good,
      cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk) *
        cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) =
      ∑ pk ∈ Good,
        cfzp030GoodLocalCredit pk.1 (pk.2 + 1)
          (cfzp030ReadyGoodShape ε W pk.1 (pk.2 + 1) (k pk) (τ pk)) := by
  apply Finset.sum_congr rfl
  intro pk hpk
  have hpair := cfzp031_prime_and_positive_exponent hAB (hGood hpk)
  exact (cfzp030GoodLocalCredit_eq_efficiency_mul_referenceMass
    hε hε2 W hpair.1 hpair.2 hsub (hτ pk hpk) (hτ4 pk hpk)
      (hready pk hpk)).symm

private theorem cfzp031_reference_mass_sum_eq_automatic_bad_sum
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (Bad : Finset (ℕ × ℕ)) :
    (∑ pk ∈ Bad,
      cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) =
      cfzp029AutomaticBadDebtEnvelope ε W Bad := by
  unfold cfzp029AutomaticBadDebtEnvelope
  apply Finset.sum_congr rfl
  intro pk hpk
  exact cfzp031PrimePowerReferenceMass_eq_badDebtEnvelope
    ε W pk.1 (pk.2 + 1)

/-- The efficiency ledger is exactly Good local credit minus automatic Bad debt. -/
theorem cfzp031EfficiencyLedger_eq_localCredit_sub_automaticBadDebt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk)) :
    cfzp031EfficiencyLedger ε W A B Good k τ =
      (∑ pk ∈ Good,
        cfzp030GoodLocalCredit pk.1 (pk.2 + 1)
          (cfzp030ReadyGoodShape ε W pk.1 (pk.2 + 1) (k pk) (τ pk))) -
      cfzp029AutomaticBadDebtEnvelope ε W
        (cfzp024BadPrimePowerPairBlockSupport A B Good) := by
  unfold cfzp031EfficiencyLedger
  rw [cfzp031_good_efficiency_sum_eq_local_credit_sum
    hε hε2 W hAB Good hGood k τ hsub hτ hτ4 hready,
    cfzp031_reference_mass_sum_eq_automatic_bad_sum]

/-! ## Gate F: one weighted signed occupancy sum -/

/-- The score attached to a block pair: positive efficiency on Good and -1 on Bad. -/
noncomputable def cfzp031OccupancyScore
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (Good : Finset (ℕ × ℕ)) (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (pk : ℕ × ℕ) : ℝ :=
  if pk ∈ Good then
    cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk)
  else -1

/-- The ledger is a single reference-mass-weighted signed occupancy sum. -/
theorem cfzp031EfficiencyLedger_eq_weighted_occupancy_sum
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (_hAB : A ≤ B) (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ) :
    cfzp031EfficiencyLedger ε W A B Good k τ =
      ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
        cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
          cfzp031OccupancyScore ε W Good k τ pk := by
  have hunion := cfzp024GoodUnionBad_eq_block Good hGood
  rw [← hunion, Finset.sum_union (cfzp024GoodDisjointBad Good)]
  unfold cfzp031EfficiencyLedger cfzp031OccupancyScore
  have hgoodSum :
      (∑ pk ∈ Good,
        cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
          if pk ∈ Good then
            cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk)
          else -1) =
        ∑ pk ∈ Good,
          cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk) *
            cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) := by
    apply Finset.sum_congr rfl
    intro pk hpk
    rw [ite_eq_left hpk]
    ring
  have hbadSum :
      (∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
        cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
          if pk ∈ Good then
            cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk)
          else -1) =
        -(∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
          cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) := by
    calc
      (∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
          cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
            if pk ∈ Good then
              cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk)
            else -1) =
        ∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
          (-cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) := by
            apply Finset.sum_congr rfl
            intro pk hpk
            rw [ite_eq_right (by exact (Finset.mem_sdiff.mp hpk).2)]
            ring
      _ = -(∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
          cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) := by
            rw [Finset.sum_neg_distrib]
  rw [hgoodSum, hbadSum]
  ring

/-! ## Gate G: finite endpoint adapter -/

/-- An efficiency-ledger bound can be supplied to the existing net-balance adapter. -/
theorem cfzp031EfficiencyLedger_bound_implies_radialContactDeficit_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (cert : Cfzp024FiniteBlockCertificate ε W A B)
    (hbad : cfzp024CertifiedBadDebtEnvelope
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good) cert.K =
      cfzp029AutomaticBadDebtEnvelope ε W
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good))
    {η : ℝ}
    (hledger : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp030CertifiedNetBalance W cert + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  exact cfzp030NetBalance_bound_implies_radialContactDeficit_le
    hε hε2 W hAB cert hbad hledger

/-! ## Firewall -/

/-- Weighted occupancy dominance and mass providers remain explicit gaps. -/
inductive Cfzp031UniversalEnvelopeEfficiencyLedgerGap : Prop
  | noIndependentWeightedOccupancyDominanceProvider
  | noPositiveWeightedDensityProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider
  | noPrimeAxisWeightedMassProvider

end DkMath.RH.CFBRCProjection
