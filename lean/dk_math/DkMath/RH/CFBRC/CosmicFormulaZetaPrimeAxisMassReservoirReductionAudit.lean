/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaReferenceMassAxisDiagnosticsAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisMassReservoirReductionAudit"

/-!
# CFZP-034: prime-axis mass reservoirs and finite residuals

This module exposes the finite prime-axis part of the reference-mass block.
The prime-axis comparison is weighted by the exact factor
`exp (-σ log p)`.  Exceptional prime-axis terms and higher-power terms are
kept as named finite residuals; neither is silently discarded.

The phase-occupancy question for primes is deliberately not solved here.
In particular, this file contains no infinite sum, density theorem, or
prime-log equidistribution provider.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Set

/-! ## Gate A: the canonical prime-axis weight -/

/-- The rectangle abscissa is strictly to the right of the critical line. -/
theorem cfzp034_rectangleSigma_gt_half
    (W : PascalCenteredXiResidueTransportWindow) :
    (1 / 2 : ℝ) < W.rectangle.σ := by
  linarith [W.rectangle.hσ]

/-- The exact sigma-decay weight attached to a prime axis point. -/
noncomputable def cfzp034PrimeAxisSigmaWeight
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))

theorem cfzp034PrimeAxisSigmaWeight_pos
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) :
    0 < cfzp034PrimeAxisSigmaWeight W p := by
  unfold cfzp034PrimeAxisSigmaWeight
  exact Real.exp_pos _

theorem cfzp034PrimeAxisSigmaWeight_lt_one
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) :
    cfzp034PrimeAxisSigmaWeight W p < 1 := by
  unfold cfzp034PrimeAxisSigmaWeight
  apply (Real.exp_lt_one_iff).2
  have hσ : 0 < W.rectangle.σ :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
      (cfzp034_rectangleSigma_gt_half W)
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hprod : 0 < W.rectangle.σ * Real.log (p : ℝ) :=
    mul_pos hσ hlog
  nlinarith

/-! ## Gate B: the reopened prime axis -/

/-- The prime-axis prefactor threshold is the exact `3 ε ≤ log p` test. -/
theorem cfzp034_two_epsilon_le_primeAxisPhaseMagnitudeLeft
    {ε : ℝ} (_hε : 0 < ε) (_hε2 : ε < Real.log 2)
    {p : ℕ} (hp : Nat.Prime p)
    (h3ε : 3 * ε ≤ Real.log (p : ℝ)) :
    2 * ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p 1 := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [cfzp033PrimePowerPhaseMagnitudeLeft_eq_logCoordinate_sub,
    cfzp033PrimePowerLogCoordinate_one]
  linarith

/-- The finite eligibility predicate used by the prime-axis reservoir. -/
def Cfzp034PrimeAxisMassEligible (ε : ℝ) (p : ℕ) : Prop :=
  3 * ε ≤ Real.log (p : ℝ) ∧ 1 ≤ Real.log (p : ℝ)

theorem cfzp034PrimeAxisMassEligible_two_epsilon_le
    {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (h : Cfzp034PrimeAxisMassEligible ε p) :
    2 * ε ≤ Real.log (p : ℝ) := by
  linarith [h.1]

theorem cfzp034PrimeAxisMassEligible_phase_left
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {p : ℕ} (hp : Nat.Prime p)
    (h : Cfzp034PrimeAxisMassEligible ε p) :
    2 * ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p 1 :=
  cfzp034_two_epsilon_le_primeAxisPhaseMagnitudeLeft hε hε2 hp h.1

/-! ## Gate C: a generic uniform-cell transport adapter -/

/-- A ready hit satisfying a supplied uniform cell has the CFZP-032 floor. -/
theorem cfzp034UniformReadyGoodEfficiencyFloor_le_of_uniformReadyCell
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ)
    (hcell : Cfzp032UniformReadyCell ε W p j k τ) :
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
      cfzp031ReadyGoodEfficiency ε W p j k τ := by
  have hphase := hcell.1
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
    (Real.sin_pos_of_pos_of_lt_pi hτ
      (by nlinarith [hτ4, Real.pi_pos])).le
  have hratio := cfzp032PhaseEfficiency_ge_sin_div_16
    (cfzpModePhaseAspectRatio_pos W).le hsub hL hR hsin hphase
  have hpref := cfzp031PrefactorEfficiency_ge_exp_div_eight hε hε2 W hp hj
    hcell.2
  have hfac := cfzp031ReadyGoodEfficiency_eq_prefactor_mul_phase
    hε hε2 W hp hj hsub hτ hτ4 hhit
  have hphaseActual :
      cfzp032ReadyGoodPhaseEfficiency ε W p j k τ ≥ Real.sin τ / 16 := by
    unfold cfzp032ReadyGoodPhaseEfficiency
    have hcontain := cfzp027_containment_of_ready_hit hhit
    have hright := hcontain.2
    have hRactual : 0 ≤ cfzpPrimePowerPhaseAngleRight ε W p j := by
      have hm := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
        hε hε2 hp hj
      rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
      exact (mul_pos W.rectangle.hT hm.2).le
    have hmono := cfzp029PhaseDerivativeCoreAbsEnvelope_mono_right
      (cfzpModePhaseAspectRatio_pos W).le hRactual hright
    have hcell' : Real.sin τ / 16 ≤
        cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ /
          cfzp029PhaseDerivativeCoreAbsEnvelope
            (cfzpModePhaseAspectRatio W)
            (cfzp026ThirdQuadrantCellRight k τ) := by
      simpa only [cfzp026PhaseCoreMargin,
        cfzp032PhaseMarginCoefficient_eq_quadratic] using hratio
    exact le_trans hcell' (by
      apply div_le_div_of_nonneg_left
      · exact (cfzp027PhaseCoreMargin_pos_of_subcritical_ready_hit
          W hsub hτ hτ4 hhit).le
      · exact (cfzp032PhaseEnvelope_pos hε hε2 W hp hj)
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
        (cfzp031PrefactorEfficiency_pos hε hε2 W hp hj).le
      exact mul_le_mul hpref hphaseActual hsin16 hpref0
    _ = cfzp031ReadyGoodEfficiency ε W p j k τ := hfac.symm

/-- The uniform floor specializes to prime-axis points at `j = 1`. -/
theorem cfzp034PrimeAxisUniformReadyGoodEfficiencyFloor_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} {τ : ℝ} (hp : Nat.Prime p)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hEligible : Cfzp034PrimeAxisMassEligible ε p) (hk : 1 ≤ k)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p 1 k τ) :
    cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
      cfzp031ReadyGoodEfficiency ε W p 1 k τ := by
  have hlarge := cfzp032LargeCellEfficiencyReady_of_one_le
    (cfzpModePhaseAspectRatio_pos W).le hsub hτ.le hτ4 hk
  have hleft := cfzp034PrimeAxisMassEligible_phase_left
    hε hε2 hp hEligible
  exact cfzp034UniformReadyGoodEfficiencyFloor_le_of_uniformReadyCell
    hε hε2 W hp (by norm_num) hsub hτ hτ4 hhit ⟨hlarge, hleft⟩

/-! ## Gate D: exact finite support partitions -/

/-- Pair support on the canonical prime axis `pk.2 = 0`. -/
def cfzp034PrimeAxisPairBlockSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  (cfzp024PrimePowerPairBlockSupport A B).filter fun pk => pk.2 = 0

/-- Pair support containing all higher prime powers. -/
def cfzp034HigherPowerPairBlockSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  (cfzp024PrimePowerPairBlockSupport A B).filter fun pk => pk.2 ≠ 0

theorem cfzp034PrimeAxisPairBlockSupport_union_higher_eq_block
    (A B : ℕ) :
    cfzp034PrimeAxisPairBlockSupport A B ∪
        cfzp034HigherPowerPairBlockSupport A B =
      cfzp024PrimePowerPairBlockSupport A B := by
  classical
  ext pk
  by_cases hzero : pk.2 = 0 <;>
    simp [cfzp034PrimeAxisPairBlockSupport,
      cfzp034HigherPowerPairBlockSupport, hzero]

theorem cfzp034PrimeAxisPairBlockSupport_disjoint_higher
    (A B : ℕ) :
    Disjoint (cfzp034PrimeAxisPairBlockSupport A B)
      (cfzp034HigherPowerPairBlockSupport A B) := by
  classical
  rw [Finset.disjoint_left]
  intro pk haxis hhigher
  simp only [cfzp034PrimeAxisPairBlockSupport, Finset.mem_filter,
    cfzp034HigherPowerPairBlockSupport, ne_eq] at haxis hhigher
  exact hhigher.2 haxis.2

/-- Eligible prime-axis pairs in a finite block. -/
def cfzp034EligiblePrimeAxisPairBlockSupport
    (ε : ℝ) (A B : ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (cfzp034PrimeAxisPairBlockSupport A B).filter
      (fun pk => Cfzp034PrimeAxisMassEligible ε pk.1)

/-- Exceptional prime-axis pairs retained as a finite residual. -/
def cfzp034ExceptionalPrimeAxisPairBlockSupport
    (ε : ℝ) (A B : ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (cfzp034PrimeAxisPairBlockSupport A B).filter
      (fun pk => ¬ Cfzp034PrimeAxisMassEligible ε pk.1)

theorem cfzp034Eligible_union_exceptional_eq_primeAxis
    (ε : ℝ) (A B : ℕ) :
    cfzp034EligiblePrimeAxisPairBlockSupport ε A B ∪
        cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B =
      cfzp034PrimeAxisPairBlockSupport A B := by
  classical
  ext pk
  by_cases h : Cfzp034PrimeAxisMassEligible ε pk.1 <;>
    simp [cfzp034EligiblePrimeAxisPairBlockSupport,
      cfzp034ExceptionalPrimeAxisPairBlockSupport, h]

theorem cfzp034Eligible_disjoint_exceptional
    (ε : ℝ) (A B : ℕ) :
    Disjoint (cfzp034EligiblePrimeAxisPairBlockSupport ε A B)
      (cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B) := by
  classical
  rw [Finset.disjoint_left]
  intro pk hgood hbad
  simp only [cfzp034EligiblePrimeAxisPairBlockSupport, Finset.mem_filter,
    cfzp034ExceptionalPrimeAxisPairBlockSupport] at hgood hbad
  exact hbad.2 hgood.2

/-! ## Finite reference-mass residuals -/

noncomputable def cfzp034EligiblePrimeAxisReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)

noncomputable def cfzp034ExceptionalPrimeAxisReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)

noncomputable def cfzp034HigherPowerReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)

theorem cfzp034BlockReferenceMass_eq_three_way_split
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (_hAB : A ≤ B) :
    cfzp032BlockReferenceMass ε W A B =
      cfzp034EligiblePrimeAxisReferenceMass ε W A B +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
        cfzp034HigherPowerReferenceMass ε W A B := by
  classical
  have h₁ := cfzp034Eligible_union_exceptional_eq_primeAxis ε A B
  have h₂ := cfzp034PrimeAxisPairBlockSupport_union_higher_eq_block A B
  have hd₁ := cfzp034Eligible_disjoint_exceptional ε A B
  have hd₂ := cfzp034PrimeAxisPairBlockSupport_disjoint_higher A B
  unfold cfzp032BlockReferenceMass cfzp034EligiblePrimeAxisReferenceMass
    cfzp034ExceptionalPrimeAxisReferenceMass cfzp034HigherPowerReferenceMass
  rw [← h₂, Finset.sum_union hd₂, ← h₁, Finset.sum_union hd₁]

/-! ## Gate E: finite sigma-weighted comparisons -/

/-- The lower constant in the prime-axis mass comparison. -/
noncomputable def cfzp034PrimeAxisMassLowerConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  2 * W.rectangle.T ^ 2 *
    Real.exp ((cfzpModePhaseAbscissa W) * ε)

/-- The upper constant in the prime-axis mass comparison. -/
noncomputable def cfzp034PrimeAxisMassUpperConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  128 * (W.rectangle.T + 1) ^ 2 *
    Real.exp ((cfzpModePhaseAbscissa W) * ε)

/-- Finite sigma weight carried by a pair support. -/
noncomputable def cfzp034PrimeAxisSigmaWeightSum
    (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S, cfzp034PrimeAxisSigmaWeight W pk.1

private theorem cfzp034_prime_axis_mass_lower_term
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hsub : Cfzp027SubcriticalPhaseAspect W) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    cfzp034PrimeAxisMassLowerConstant ε W *
        cfzp034PrimeAxisSigmaWeight W pk.1 ≤
      cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) := by
  classical
  have haxis := (Finset.mem_filter.mp hpk).1
  have heligible := (Finset.mem_filter.mp hpk).2
  have hblock := (Finset.mem_filter.mp haxis).1
  have hzero := (Finset.mem_filter.mp haxis).2
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hblock)
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hmass := cfzp033PrimeAxisReferenceMass_lower hε hε2 W hsub
    hp (cfzp034PrimeAxisMassEligible_two_epsilon_le hε heligible)
      heligible.2
  have hmass' : cfzp034PrimeAxisMassLowerConstant ε W *
        cfzp034PrimeAxisSigmaWeight W pk.1 ≤
      cfzp033PrimeAxisReferenceMass ε W pk.1 := by
    simpa [cfzp034PrimeAxisMassLowerConstant,
      cfzp034PrimeAxisSigmaWeight] using hmass
  simpa [cfzp033PrimeAxisReferenceMass, hzero] using hmass'

private theorem cfzp034_prime_axis_mass_upper_term
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hsub : Cfzp027SubcriticalPhaseAspect W) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) ≤
      cfzp034PrimeAxisMassUpperConstant ε W *
      cfzp034PrimeAxisSigmaWeight W pk.1 := by
  classical
  have haxis := (Finset.mem_filter.mp hpk).1
  have heligible := (Finset.mem_filter.mp hpk).2
  have hblock := (Finset.mem_filter.mp haxis).1
  have hzero := (Finset.mem_filter.mp haxis).2
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hblock)
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hmass := cfzp033PrimeAxisReferenceMass_upper hε hε2 W hsub
    hp (cfzp034PrimeAxisMassEligible_two_epsilon_le hε heligible)
      heligible.2
  have hmass' : cfzp033PrimeAxisReferenceMass ε W pk.1 ≤
      cfzp034PrimeAxisMassUpperConstant ε W *
        cfzp034PrimeAxisSigmaWeight W pk.1 := by
    simpa [cfzp034PrimeAxisMassUpperConstant,
      cfzp034PrimeAxisSigmaWeight] using hmass
  simpa [cfzp033PrimeAxisReferenceMass, hzero] using hmass'

theorem cfzp034PrimeAxisSigmaWeightSum_lower
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    cfzp034PrimeAxisMassLowerConstant ε W *
        cfzp034PrimeAxisSigmaWeightSum W S ≤
      cfzp032GoodReferenceMass ε W S := by
  classical
  unfold cfzp034PrimeAxisSigmaWeightSum cfzp032GoodReferenceMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro pk hpk
  exact cfzp034_prime_axis_mass_lower_term hε hε2 W hAB hsub (hS hpk)

theorem cfzp034PrimeAxisSigmaWeightSum_upper
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B) :
    cfzp032GoodReferenceMass ε W S ≤
      cfzp034PrimeAxisMassUpperConstant ε W *
      cfzp034PrimeAxisSigmaWeightSum W S := by
  classical
  unfold cfzp034PrimeAxisSigmaWeightSum cfzp032GoodReferenceMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro pk hpk
  exact cfzp034_prime_axis_mass_upper_term hε hε2 W hAB hsub (hS hpk)

/-! ## Gate F: the eligible and residual finite masses -/

theorem cfzp034EligiblePrimeAxisReferenceMass_upper
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hsub : Cfzp027SubcriticalPhaseAspect W) :
    cfzp034EligiblePrimeAxisReferenceMass ε W A B ≤
      cfzp034PrimeAxisMassUpperConstant ε W *
        cfzp034PrimeAxisSigmaWeightSum W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) := by
  classical
  exact cfzp034PrimeAxisSigmaWeightSum_upper hε hε2 W hAB hsub _ (by
    intro pk hpk
    exact hpk)

/-! ## Gate G: finite reservoir reduction to the radial endpoint -/

/--
The finite prime-axis reservoir inequality is sufficient for the CFZP-032
radial contact endpoint.  The exceptional and higher-power masses remain
visible in the hypothesis, so this theorem does not hide a residual estimate.
-/
theorem cfzp034PrimeAxisReservoir_implies_radialContactDeficit_le
    {ε ρ η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hk : ∀ pk ∈ Good, 1 ≤ k pk)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W pk.1 1
        (k pk) (τ pk))
    (hfloor : ∀ pk ∈ Good,
      ρ ≤ cfzp032UniformReadyGoodEfficiencyFloor ε W (τ pk))
    (hρ : 0 ≤ ρ)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B +
          cfzp034PrimeAxisMassUpperConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) ≤
        (1 + ρ) * cfzp034PrimeAxisMassLowerConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W Good + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  classical
  have hGoodBlock : Good ⊆ cfzp024PrimePowerPairBlockSupport A B := by
    intro pk hpk
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hGood hpk)).1).1
  have hfloor' : ∀ pk ∈ Good, ρ ≤
      cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1)
        (k pk) (τ pk) := by
    intro pk hpk
    have haxis := (Finset.mem_filter.mp (hGood hpk)).1
    have hzero := (Finset.mem_filter.mp haxis).2
    have heligible := (Finset.mem_filter.mp (hGood hpk)).2
    have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
      (cfzp024PrimePowerPairBlockSupport_subset_right hAB
        ((Finset.mem_filter.mp haxis).1))
    have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
    have hgoodEff := cfzp034PrimeAxisUniformReadyGoodEfficiencyFloor_le
      hε hε2 W hp hsub (hτ pk hpk) (hτ4 pk hpk) heligible
        (hk pk hpk) (hready pk hpk)
    have hactual := le_trans (hfloor pk hpk) hgoodEff
    simpa [hzero] using hactual
  have hcov :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp032BlockReferenceMass ε W A B ≤
        (1 + ρ) * cfzp032GoodReferenceMass ε W Good + η := by
    have hsplit := cfzp034BlockReferenceMass_eq_three_way_split ε W hAB
    have hupper := cfzp034EligiblePrimeAxisReferenceMass_upper
      hε hε2 W hAB hsub
    have hlow := cfzp034PrimeAxisSigmaWeightSum_lower hε hε2 W hAB
      hsub Good hGood
    have hscale :
        (1 + ρ) * cfzp034PrimeAxisMassLowerConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W Good ≤
          (1 + ρ) * cfzp032GoodReferenceMass ε W Good := by
      have hnonneg : 0 ≤ 1 + ρ := by linarith
      calc
        (1 + ρ) * cfzp034PrimeAxisMassLowerConstant ε W *
              cfzp034PrimeAxisSigmaWeightSum W Good =
            (1 + ρ) * (cfzp034PrimeAxisMassLowerConstant ε W *
              cfzp034PrimeAxisSigmaWeightSum W Good) := by ring
        _ ≤ (1 + ρ) * cfzp032GoodReferenceMass ε W Good :=
          mul_le_mul_of_nonneg_left hlow hnonneg
    rw [hsplit]
    nlinarith
  have hready' : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W pk.1 (pk.2 + 1)
        (k pk) (τ pk) := by
    intro pk hpk
    have hzero := (Finset.mem_filter.mp
      (Finset.mem_filter.mp (hGood hpk)).1).2
    simpa [hzero] using hready pk hpk
  apply cfzp032_weightedCoverage_implies_radialContactDeficit_le
    hε hε2 W hAB Good hGoodBlock k τ hsub hτ hτ4 hready' hfloor'
      hcov

/-! ## Gate H: higher-power sigma normalization -/

theorem cfzp034PrimePowerSigmaWeight_eq_primeAxisWeight_pow
    (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    Real.exp (-(W.rectangle.σ) *
        cfzp033PrimePowerLogCoordinate p j) =
      (cfzp034PrimeAxisSigmaWeight W p) ^ j := by
  unfold cfzp034PrimeAxisSigmaWeight cfzp033PrimePowerLogCoordinate
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-! ## Firewall -/

inductive Cfzp034PrimeAxisMassReservoirGap : Prop
  | noPrimeAxisWeightedGoodPhaseOccupancyProvider
  | noPrimeLogPhaseDistributionProvider
  | noAutomaticWeightedCoverageProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
  | noAutomaticSubcriticalWindowProvider

end DkMath.RH.CFBRCProjection
