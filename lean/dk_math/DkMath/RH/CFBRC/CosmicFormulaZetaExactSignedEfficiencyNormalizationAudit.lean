/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisMassReservoirReductionAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaExactSignedEfficiencyNormalizationAudit"

/-!
# CFZP-035: exact signed efficiency normalization

The CFZP-034 reservoir uses deliberately coarse lower and upper constants.
This module records the corresponding finite coefficient obstruction and then
normalizes each actual branch-free event by its positive reference mass.
The resulting score is the actual event divided by the reference mass, not a
binary Good/Bad certificate score.  It retains its sign on every safe
prime-power mode and remains in `[-1, 1]`.

All identities below are finite.  No prime distribution, infinite sum,
limit exchange, residual elimination, or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory

/-! ## Gate A: the coarse finite obstruction -/

/-- The coarse CFZP-034 constants differ by more than a factor of 64. -/
theorem cfzp035_coarsePrimeAxisMassUpper_gt_64_lower
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    64 * cfzp034PrimeAxisMassLowerConstant ε W <
      cfzp034PrimeAxisMassUpperConstant ε W := by
  unfold cfzp034PrimeAxisMassLowerConstant
    cfzp034PrimeAxisMassUpperConstant
  have hT : 0 < W.rectangle.T := W.rectangle.hT
  have hE : 0 < Real.exp ((cfzpModePhaseAbscissa W) * ε) :=
    Real.exp_pos _
  nlinarith [sq_nonneg W.rectangle.T]

/-! ## Gate B: exact signed efficiency -/

/--
The actual branch-free event divided by its positive reference mass.  This
is an exact signed score, rather than CFZP-031's binary certificate score.
-/
noncomputable def cfzp035PrimePowerSignedEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzpPrimePowerBranchFreeTrigEvent ε W p j /
    cfzp031PrimePowerReferenceMass ε W p j

/-- Multiplication by the reference mass recovers the actual event exactly. -/
theorem cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j =
      cfzp031PrimePowerReferenceMass ε W p j *
        cfzp035PrimePowerSignedEfficiency ε W p j := by
  unfold cfzp035PrimePowerSignedEfficiency
  have hμ := cfzp031PrimePowerReferenceMass_pos hε hε2 W hp hj
  field_simp [ne_of_gt hμ]

/-- The exact signed score has absolute value at most one. -/
theorem cfzp035PrimePowerSignedEfficiency_abs_le_one
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    |cfzp035PrimePowerSignedEfficiency ε W p j| ≤ 1 := by
  have hμ := cfzp031PrimePowerReferenceMass_pos hε hε2 W hp hj
  have hevent := cfzp029PrimePowerBranchFreeTrigEvent_abs_le
    hε hε2 W hp hj
  have hμenv := cfzp031PrimePowerReferenceMass_eq_badDebtEnvelope
    ε W p j
  unfold cfzp035PrimePowerSignedEfficiency
  rw [abs_div, abs_of_pos hμ]
  apply (div_le_iff₀ hμ).2
  simpa [hμenv] using hevent

theorem cfzp035PrimePowerSignedEfficiency_lower_bound
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    -1 ≤ cfzp035PrimePowerSignedEfficiency ε W p j := by
  exact (abs_le.mp (cfzp035PrimePowerSignedEfficiency_abs_le_one
    hε hε2 W hp hj)).1

theorem cfzp035PrimePowerSignedEfficiency_upper_bound
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzp035PrimePowerSignedEfficiency ε W p j ≤ 1 := by
  exact (abs_le.mp (cfzp035PrimePowerSignedEfficiency_abs_le_one
    hε hε2 W hp hj)).2

/-! ## Gate C: ready Good certificates bound the actual score -/

/-- Ready Good efficiency is a lower bound for the actual signed score. -/
theorem cfzp031ReadyGoodEfficiency_le_cfzp035PrimePowerSignedEfficiency
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    cfzp031ReadyGoodEfficiency ε W p j k τ ≤
      cfzp035PrimePowerSignedEfficiency ε W p j := by
  have hμ := cfzp031PrimePowerReferenceMass_pos hε hε2 W hp hj
  have hcredit := cfzp030PrimePowerBranchFreeTrigEvent_ge_readyFactorizedCredit
    hε hε2 W hp hj hsub hτ hτ4 hhit
  rw [cfzp030GoodLocalCredit_eq_efficiency_mul_referenceMass
    hε hε2 W hp hj hsub hτ hτ4 hhit] at hcredit
  rw [cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    hε hε2 W hp hj] at hcredit
  unfold cfzp035PrimePowerSignedEfficiency
  apply le_of_mul_le_mul_right ?_ hμ
  calc
    cfzp031ReadyGoodEfficiency ε W p j k τ *
        cfzp031PrimePowerReferenceMass ε W p j ≤
      cfzp031PrimePowerReferenceMass ε W p j *
        cfzp035PrimePowerSignedEfficiency ε W p j := hcredit
    _ = cfzp035PrimePowerSignedEfficiency ε W p j *
        cfzp031PrimePowerReferenceMass ε W p j := by ring

/-- The CFZP-034 uniform floor is also a lower bound for the actual score. -/
theorem cfzp034UniformReadyGoodEfficiencyFloor_le_cfzp035PrimePowerSignedEfficiency
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ)
    (hcell : Cfzp032UniformReadyCell ε W p j k τ) :
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
      cfzp035PrimePowerSignedEfficiency ε W p j := by
  exact le_trans
    (cfzp034UniformReadyGoodEfficiencyFloor_le_of_uniformReadyCell
      hε hε2 W hp hj hsub hτ hτ4 hhit hcell)
    (cfzp031ReadyGoodEfficiency_le_cfzp035PrimePowerSignedEfficiency
      hε hε2 W hp hj hsub hτ hτ4 hhit)

/-- Prime-axis specialization of the actual-score floor. -/
theorem cfzp034PrimeAxisUniformReadyGoodEfficiencyFloor_le_cfzp035PrimePowerSignedEfficiency
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} {τ : ℝ} (hp : Nat.Prime p)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hEligible : Cfzp034PrimeAxisMassEligible ε p) (hk : 1 ≤ k)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p 1 k τ) :
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
      cfzp035PrimePowerSignedEfficiency ε W p 1 := by
  have hcell : Cfzp032UniformReadyCell ε W p 1 k τ := by
    refine ⟨cfzp032LargeCellEfficiencyReady_of_one_le
      (cfzpModePhaseAspectRatio_pos W).le hsub hτ.le hτ4 hk, ?_⟩
    exact cfzp034PrimeAxisMassEligible_phase_left hε hε2 hp hEligible
  exact cfzp034UniformReadyGoodEfficiencyFloor_le_cfzp035PrimePowerSignedEfficiency
    hε hε2 W hp (by norm_num) hsub hτ hτ4 hhit hcell

/-! ## Gate D/E: exact signed block and radial recurrence -/

/-- The exact signed-efficiency contribution of a finite pair support. -/
noncomputable def cfzp035SignedEfficiencyMassOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
      cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1)

/-- The exact signed efficiency sum over a canonical finite block. -/
noncomputable def cfzp035SignedEfficiencyBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp035SignedEfficiencyMassOn ε W
    (cfzp024PrimePowerPairBlockSupport A B)

private theorem cfzp035_block_pair_safe
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

theorem cfzp035SignedEfficiencyBlock_eq_branchFreeTrigEventBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp035SignedEfficiencyBlock ε W A B =
      ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
        cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1) := by
  classical
  unfold cfzp035SignedEfficiencyBlock cfzp035SignedEfficiencyMassOn
  apply Finset.sum_congr rfl
  intro pk hpk
  obtain ⟨hp, hj⟩ := cfzp035_block_pair_safe hAB hpk
  exact (cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    hε hε2 W hp hj).symm

theorem cfzp035SignedEfficiencyBlock_eq_vonMangoldtPulseBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp035SignedEfficiencyBlock ε W A B =
      cfzp022VonMangoldtPulseBlock ε W A B := by
  classical
  rw [cfzp035SignedEfficiencyBlock_eq_branchFreeTrigEventBlock hε hε2 W hAB]
  have hpos := cfzp024BlockPositiveEventMass_eq_supportDifferenceSum ε W hAB
  have hneg := cfzp024BlockNegativeEventDebt_eq_supportDifferenceSum ε W hAB
  have hpulse := cfzp022VonMangoldtPulseBlock_eq_blockPositiveMass_sub_blockNegativeDebt
    hε hε2 W hAB
  rw [hpulse, hpos, hneg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pk hpk
  exact cfzp019PrimePowerEvent_eq_positiveMass_sub_negativeDebt
    ε W pk.1 (pk.2 + 1)

theorem cfzp035SignedEfficiencyBlock_eq_branchFreeTrigLedger_sub
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp035SignedEfficiencyBlock ε W A B =
      cfzpPrimePowerBranchFreeTrigLedger ε W B -
        cfzpPrimePowerBranchFreeTrigLedger ε W A := by
  rw [cfzp035SignedEfficiencyBlock_eq_vonMangoldtPulseBlock hε hε2 W hAB]
  exact (cfzp022BranchFreeTrigLedger_block_sub_eq_pulseBlock
    hε hε2 W hAB).symm

theorem cfzp035RadialContactDeficit_eq_sub_signedEfficiencyBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A -
        cfzp035SignedEfficiencyBlock ε W A B := by
  rw [cfzp022RadialContactDeficit_block_eq_sub_pulseBlock hε W hAB,
    ← cfzp035SignedEfficiencyBlock_eq_vonMangoldtPulseBlock hε hε2 W hAB]

theorem cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (h : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp035SignedEfficiencyBlock ε W A B + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  rw [cfzp035RadialContactDeficit_eq_sub_signedEfficiencyBlock hε hε2 W hAB]
  linarith

/-! ## Gate F: exact signed three-way decomposition -/

theorem cfzp035SignedEfficiencyBlock_eq_three_way_split
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (_hAB : A ≤ B) :
    cfzp035SignedEfficiencyBlock ε W A B =
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) +
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B) +
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp034HigherPowerPairBlockSupport A B) := by
  classical
  have h₁ := cfzp034Eligible_union_exceptional_eq_primeAxis ε A B
  have h₂ := cfzp034PrimeAxisPairBlockSupport_union_higher_eq_block A B
  have hd₁ := cfzp034Eligible_disjoint_exceptional ε A B
  have hd₂ := cfzp034PrimeAxisPairBlockSupport_disjoint_higher A B
  unfold cfzp035SignedEfficiencyBlock cfzp035SignedEfficiencyMassOn
  rw [← h₂, Finset.sum_union hd₂, ← h₁, Finset.sum_union hd₁]

theorem cfzp035SignedEfficiencyResiduals_bound_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (h : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      (cfzp035SignedEfficiencyMassOn ε W
        (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) +
       cfzp035SignedEfficiencyMassOn ε W
        (cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B) +
       cfzp035SignedEfficiencyMassOn ε W
        (cfzp034HigherPowerPairBlockSupport A B)) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  apply cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le
    hε hε2 W hAB
  rw [cfzp035SignedEfficiencyBlock_eq_three_way_split ε W hAB]
  exact h

/-! ## Gate G: exact prime-axis sigma-weighted signed amplitude -/

/-- The signed amplitude left after extracting the exact sigma weight. -/
noncomputable def cfzp035PrimeAxisSignedAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    Real.exp ((cfzpModePhaseAbscissa W) * ε) *
    cfzp033ReferenceMassReducedShape ε W (Real.log (p : ℝ)) *
    cfzp035PrimePowerSignedEfficiency ε W p 1

theorem cfzp035PrimeAxisEvent_eq_sigmaWeight_mul_signedAmplitude
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (hp : Nat.Prime p) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p 1 =
      cfzp034PrimeAxisSigmaWeight W p *
        cfzp035PrimeAxisSignedAmplitude ε W p := by
  rw [cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    hε hε2 W hp (by norm_num)]
  rw [cfzp033PrimePowerReferenceMass_eq_sigma_decay hε hε2 W hp
    (by norm_num), cfzp033PrimePowerLogCoordinate_one]
  unfold cfzp034PrimeAxisSigmaWeight cfzp035PrimeAxisSignedAmplitude
  ring

theorem cfzp035EligiblePrimeAxisSignedEfficiencyMass_eq_weightedAmplitude
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp035SignedEfficiencyMassOn ε W
        (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) =
      ∑ pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B,
        cfzp034PrimeAxisSigmaWeight W pk.1 *
          cfzp035PrimeAxisSignedAmplitude ε W pk.1 := by
  classical
  unfold cfzp035SignedEfficiencyMassOn
  apply Finset.sum_congr rfl
  intro pk hpk
  have haxis := (Finset.mem_filter.mp hpk).1
  have hblock := (Finset.mem_filter.mp haxis).1
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hblock)
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hzero := (Finset.mem_filter.mp haxis).2
  have hevent := cfzp035PrimeAxisEvent_eq_sigmaWeight_mul_signedAmplitude
    hε hε2 W hp
  rw [cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    hε hε2 W hp (by norm_num)] at hevent
  simpa [hzero] using hevent

/-! ## Firewall -/

inductive Cfzp035ExactSignedEfficiencyNormalizationGap : Prop
  | noPrimeAxisSignedScoreDominanceProvider
  | noPrimeLogSignedPhaseDistributionProvider
  | noAutomaticSubcriticalWindowProvider

end DkMath.RH.CFBRCProjection
