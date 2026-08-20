/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExplicitSmoothMarginRadialBudgetAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerSigmaTailEnvelopeAudit"

/-!
# CFZP-045: a finite sigma-tail envelope for higher prime powers

This module keeps the higher-power ledger finite.  The exact sigma decay is
retained term by term, and the late carrier-cell specialization is transported
to the explicit radial budget from CFZP-044.  Bounds on the size or decay of
the resulting finite tail are deliberately left as named interfaces.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gates A-B: support and logarithmic coordinates -/

/-- The actual exponent of a higher-power pair is at least two. -/
theorem cfzp045HigherPowerActualExponent_two_le
    {A B : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport A B) :
    2 ≤ pk.2 + 1 := by
  have hne := (Finset.mem_filter.mp hpk).2
  omega

/-- Every higher-power block pair has a prime base. -/
theorem cfzp045HigherPower_basePrime
    {A B : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport A B) :
    Nat.Prime pk.1 := by
  have hblock := (Finset.mem_filter.mp hpk).1
  have hright := (Finset.mem_sdiff.mp hblock).1
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hright
  exact (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1

/-- The prime logarithm divided by its prime-power coordinate is `1 / j`. -/
theorem cfzp045_log_div_primePowerLogCoordinate_eq_inv
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    Real.log (p : ℝ) /
        cfzp033PrimePowerLogCoordinate p j =
      1 / (j : ℝ) := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  unfold cfzp033PrimePowerLogCoordinate
  field_simp

/-! ## Gate C: the per-pair envelope -/

/-- The constant in the fixed-prime higher-power upper envelope. -/
noncomputable def cfzp045HigherPowerReferenceMassConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  128 * (W.rectangle.T + 1) ^ 2 *
    Real.exp (cfzpModePhaseAbscissa W * ε)

/-- The finite sigma envelope assigned to one prime-power pair. -/
noncomputable def cfzp045HigherPowerSigmaEnvelopeTerm
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp045HigherPowerReferenceMassConstant ε W *
    (cfzp034PrimeAxisSigmaWeight W p) ^ j / (j : ℝ)

/-- The 033 fixed-prime upper bound in exact sigma-weight form. -/
theorem cfzp045PrimePowerReferenceMass_le_sigmaEnvelopeTerm
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsafe2 : 2 * ε ≤ cfzp033PrimePowerLogCoordinate p j)
    (hsafe1 : 1 ≤ cfzp033PrimePowerLogCoordinate p j) :
    cfzp031PrimePowerReferenceMass ε W p j ≤
      cfzp045HigherPowerSigmaEnvelopeTerm ε W p j := by
  have hmass := cfzp033FixedPrimeReferenceMass_upper hε hε2 W hsub
    hp hj hsafe2 hsafe1
  rw [cfzp034PrimePowerSigmaWeight_eq_primeAxisWeight_pow] at hmass
  simpa [cfzp045HigherPowerSigmaEnvelopeTerm,
    cfzp045HigherPowerReferenceMassConstant, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hmass

/-! ## Gates D-E: a finite higher-power tail and its block comparison -/

/-- The sigma-weighted higher-power tail over one finite pair block. -/
noncomputable def cfzp045HigherPowerSigmaTail
    (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
    (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
      ((pk.2 + 1 : ℕ) : ℝ)

/-- Every finite sigma tail is nonnegative term by term. -/
theorem cfzp045HigherPowerSigmaTail_nonneg
    (W : PascalCenteredXiResidueTransportWindow) (A B : ℕ) :
    0 ≤ cfzp045HigherPowerSigmaTail W A B := by
  unfold cfzp045HigherPowerSigmaTail
  apply Finset.sum_nonneg
  intro pk hpk
  have hj : 0 < pk.2 + 1 := by omega
  exact div_nonneg
    (pow_nonneg (cfzp034PrimeAxisSigmaWeight_pos W pk.1).le _)
    (by exact_mod_cast hj.le)

/-- Safety conditions for applying the fixed-prime upper bound on a block. -/
def Cfzp045HigherPowerBlockSafe
    (ε : ℝ) (A B : ℕ) : Prop :=
  ∀ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
    2 * ε ≤ cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) ∧
    1 ≤ cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1)

/-- The raw higher-power reference mass is bounded by its finite sigma tail. -/
theorem cfzp045HigherPowerReferenceMass_le_sigmaTail
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    {A B : ℕ}
    (hsafe : Cfzp045HigherPowerBlockSafe ε A B) :
    cfzp034HigherPowerReferenceMass ε W A B ≤
      cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp045HigherPowerSigmaTail W A B := by
  classical
  unfold cfzp034HigherPowerReferenceMass cfzp045HigherPowerSigmaTail
  calc
    (∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
        cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) ≤
      ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
        cfzp045HigherPowerSigmaEnvelopeTerm ε W pk.1 (pk.2 + 1) := by
          apply Finset.sum_le_sum
          intro pk hpk
          exact cfzp045PrimePowerReferenceMass_le_sigmaEnvelopeTerm
            hε hε2 W hsub (cfzp045HigherPower_basePrime hpk)
            (by omega) (hsafe pk hpk).1 (hsafe pk hpk).2
    _ = cfzp045HigherPowerReferenceMassConstant ε W *
        ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
          (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
            ((pk.2 + 1 : ℕ) : ℝ) := by
          simp only [cfzp045HigherPowerSigmaEnvelopeTerm]
          calc
            (∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
                cfzp045HigherPowerReferenceMassConstant ε W *
                  (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
                    ((pk.2 + 1 : ℕ) : ℝ)) =
              ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
                cfzp045HigherPowerReferenceMassConstant ε W *
                  ((cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
                    ((pk.2 + 1 : ℕ) : ℝ)) := by
                apply Finset.sum_congr rfl
                intro pk hpk
                ring
            _ = cfzp045HigherPowerReferenceMassConstant ε W *
                ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
                  (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
                    ((pk.2 + 1 : ℕ) : ℝ) := by
                rw [Finset.mul_sum]

/-! ## Gates F-G: late carrier cells -/

private theorem cfzp045_two_pow_succ_gt
    (k : ℕ) : k < 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      have hstep : k + 1 < 2 ^ (k + 1) * 2 := by omega
      simpa [Nat.pow_succ, Nat.add_assoc] using hstep

/-- A late natural carrier cell satisfies the higher-power safety predicate. -/
theorem cfzp045CarrierCellHigherPowerBlockSafe
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    Cfzp045HigherPowerBlockSafe ε
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  intro pk hpk
  have hAB : cfzp040CarrierCellNaturalLeft W c n ≤
      cfzp040CarrierCellNaturalRight W c n :=
    cfzp041CarrierCellNaturalLeft_le_right W c n
  have hblock := (Finset.mem_filter.mp hpk).1
  have hright : pk ∈ pascalPrimePowerPairSupportUpTo
      (cfzp040CarrierCellNaturalRight W c n) :=
    (Finset.mem_sdiff.mp hblock).1
  have hleft : pk ∉ pascalPrimePowerPairSupportUpTo
      (cfzp040CarrierCellNaturalLeft W c n) :=
    (Finset.mem_sdiff.mp hblock).2
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hright
  have hp : Nat.Prime pk.1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hj : 0 < pk.2 + 1 := by omega
  have hqpos : 0 < pk.1 ^ (pk.2 + 1) := Nat.pow_pos hp.pos
  have hqne : pk.1 ^ (pk.2 + 1) ≠ 0 := hqpos.ne'
  have hqleB : pk.1 ^ (pk.2 + 1) ≤
      cfzp040CarrierCellNaturalRight W c n := hs.2.2
  have hqgtA : cfzp040CarrierCellNaturalLeft W c n <
      pk.1 ^ (pk.2 + 1) := by
    by_contra hnot
    have hqleA : pk.1 ^ (pk.2 + 1) ≤
        cfzp040CarrierCellNaturalLeft W c n := Nat.le_of_not_gt hnot
    have hpow_exp : pk.2 < pk.1 ^ (pk.2 + 1) := by
      exact (cfzp045_two_pow_succ_gt pk.2).trans_le
        (Nat.pow_le_pow_left hp.two_le (pk.2 + 1))
    have hbase_le : pk.1 ≤ pk.1 ^ (pk.2 + 1) := by
      simpa [pow_one] using
        (Nat.pow_le_pow_right hp.one_lt.le (by omega : 1 ≤ pk.2 + 1))
    have hleft_mem : pk ∈ pascalPrimePowerPairSupportUpTo
        (cfzp040CarrierCellNaturalLeft W c n) := by
      rw [mem_pascalPrimePowerPairSupportUpTo_iff]
      refine ⟨mem_pascalPrimeCoordinateSupportUpTo_iff.mpr
          ⟨hp, le_trans hbase_le hqleA⟩,
        lt_of_lt_of_le hpow_exp hqleA, hqleA⟩
    exact hleft hleft_mem
  have hqL : cfzp040CarrierCellExpLeft W c n <
      ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
    apply (Nat.floor_lt' hqne).mp
    simpa [cfzp040CarrierCellNaturalLeft] using hqgtA
  have hqR : ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) ≤
      cfzp040CarrierCellExpRight W c n := by
    apply (Nat.le_floor_iff' hqne).mp
    simpa [cfzp040CarrierCellNaturalRight] using hqleB
  have hlogL : cfzp039CarrierCellLeft W c n <
      Real.log ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
    have hqposR : (0 : ℝ) < ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hqpos
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hqposR]
    simpa [cfzp040CarrierCellExpLeft] using hqL
  have hlogR : Real.log ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) ≤
      cfzp039CarrierCellRight W c n := by
    have hqposR : (0 : ℝ) < ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hqpos
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hqposR]
    simpa [cfzp040CarrierCellExpRight] using hqR
  have hcoord : cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) =
      Real.log ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
    simp [cfzp033PrimePowerLogCoordinate, Nat.cast_pow, Real.log_pow]
  have hlate := max_le_iff.mp hLate
  rw [hcoord]
  constructor <;> linarith [hlogL]

/-- The late carrier-cell higher-power mass has the sigma-tail envelope. -/
theorem cfzp045CarrierCellHigherPowerReferenceMass_le_sigmaTail
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp034HigherPowerReferenceMass ε W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp045HigherPowerSigmaTail W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) := by
  apply cfzp045HigherPowerReferenceMass_le_sigmaTail hε hε2 W hsub
  exact cfzp045CarrierCellHigherPowerBlockSafe W c n
    (cfzp044_eligibilityThreshold_le_of_radialLate hLate)

/-! ## Gate H: the sigma-tail radial budget -/

/-- The CFZP-044 budget with the higher-power mass replaced by a finite tail. -/
def Cfzp045SigmaTailExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) +
    cfzp045HigherPowerReferenceMassConstant ε W *
      cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) + D ≤
    cfzp044ExplicitSmoothMargin ε W c n + η

/-- A sigma-tail budget implies the CFZP-044 radial endpoint bound. -/
theorem cfzp045SigmaTailExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hSmoothLog :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n)
    (hf_diff : ∀ t ∈ Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
      ε W c n D)
    (hbudget : Cfzp045SigmaTailExplicitSmoothMarginBudgetAt ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  have hcell := cfzp044_eligibilityThreshold_le_of_radialLate hLate
  have htail := cfzp045CarrierCellHigherPowerReferenceMass_le_sigmaTail
    hε hε2 W hsub c n hLate
  have hbudget044 : Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n := by
    unfold Cfzp045SigmaTailExplicitSmoothMarginBudgetAt at hbudget
    unfold Cfzp044ExplicitSmoothMarginBudgetAt
    linarith
  exact cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    hε hε2 W c n hM hLate hSmoothLog hf_diff hf_int hM_int hD_int hD
    hbudget044

/-! ## Firewall -/

/-- Open providers for the remaining finite-tail and cofinal questions. -/
inductive Cfzp045HigherPrimePowerSigmaTailEnvelopeGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noHigherPowerSigmaTailCardinalityBound
  | noHigherPowerSigmaTailExponentialDecay
  | noCofinalSigmaTailExplicitSmoothMarginBudgetProvider

end DkMath.RH.CFBRCProjection
