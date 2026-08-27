/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaUniversalPrimePowerBadDebtEnvelopeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaWeightedPrimePowerCreditDebtFactorizationAudit"

/-!
# CFZP-030: weighted prime-power credit/debt factorization

This module gives the Good credit and automatic Bad debt the same explicit
prime-power carrier.  It is a finite normalization layer: it does not provide
a weighted dominance provider, an infinite-sum statement, a limit exchange,
or an RH conclusion.

The carrier is
`2 * log p * cfzpModeCriticalScale (p ^ j)`.  The existing critical scale is
`exp (-(1 / 2) * log n)`, and its prime-power exponent form is recorded without
introducing asymptotic notation.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set

/-! ## Gate A/B: the common critical carrier -/

/-- The arithmetic carrier shared by Good credit and Bad debt. -/
noncomputable def cfzp030PrimePowerCriticalCarrier
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j)

/-- The common carrier is positive for every prime with positive exponent. -/
theorem cfzp030PrimePowerCriticalCarrier_pos
    {p j : ℕ} (hp : Nat.Prime p) (_hj : 0 < j) :
    0 < cfzp030PrimePowerCriticalCarrier p j := by
  unfold cfzp030PrimePowerCriticalCarrier
  exact mul_pos
    (mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hp.one_lt)))
    (cfzpModeCriticalScale_pos (p ^ j))

/-- The critical scale on a prime power in exponential/logarithmic normal form. -/
theorem cfzp030ModeCriticalScale_prime_pow_eq_exp
    (p j : ℕ) :
    cfzpModeCriticalScale (p ^ j) =
      Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ)) := by
  unfold cfzpModeCriticalScale
  rw [show ((p ^ j : ℕ) : ℝ) = (p : ℝ) ^ j by norm_num,
    Real.log_pow]
  congr 1
  ring

/-- The carrier rewritten using the prime-power exponent. -/
theorem cfzp030PrimePowerCriticalCarrier_eq_exp
    (p j : ℕ) :
    cfzp030PrimePowerCriticalCarrier p j =
      2 * Real.log (p : ℝ) *
        Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ)) := by
  unfold cfzp030PrimePowerCriticalCarrier
  rw [cfzp030ModeCriticalScale_prime_pow_eq_exp]

/-! ## Gate C: Good local credit factorization -/

/-- A normalized Good local shape multiplied by the common carrier. -/
noncomputable def cfzp030GoodLocalCredit
    (p j : ℕ) (κ : ℝ) : ℝ :=
  cfzp030PrimePowerCriticalCarrier p j * κ

/-- The CFZP-024 Good sum uses exactly the common-carrier normal form. -/
theorem cfzp030CertifiedGoodCredit_eq_carrier_sum
    (Good : Finset (ℕ × ℕ)) (κ : ℕ × ℕ → ℝ) :
    cfzp024CertifiedGoodCredit Good κ =
      ∑ pk ∈ Good,
        cfzp030PrimePowerCriticalCarrier pk.1 (pk.2 + 1) * (κ pk) := by
  unfold cfzp024CertifiedGoodCredit cfzp030PrimePowerCriticalCarrier
  simp only

/-- The normalized shape delivered by a ready periodic Good hit. -/
noncomputable def cfzp030ReadyGoodShape
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : ℝ :=
  cfzp025CenteredDerivativePrefactorFloor ε W p j *
    cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ

/-- The ready-hit Good credit is the common carrier times its local shape. -/
theorem cfzp030ReadyGoodLocalCredit_eq
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) :
    cfzp030GoodLocalCredit p j
        (cfzp030ReadyGoodShape ε W p j k τ) =
      cfzp030PrimePowerCriticalCarrier p j *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j *
          cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ) := by
  unfold cfzp030GoodLocalCredit cfzp030ReadyGoodShape
  ring

/-- A ready hit makes the normalized Good shape strictly positive. -/
theorem cfzp030ReadyGoodShape_pos_of_subcritical_ready_hit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    0 < cfzp030ReadyGoodShape ε W p j k τ := by
  unfold cfzp030ReadyGoodShape
  exact mul_pos
    (cfzp025CenteredDerivativePrefactorFloor_pos hε hε2 W hp hj)
    (cfzp027PhaseCoreMargin_pos_of_subcritical_ready_hit
      W hsub hτ hτ4 hhit)

/-- A ready hit supplies the factorized Good credit bound for the event. -/
theorem cfzp030PrimePowerBranchFreeTrigEvent_ge_readyFactorizedCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    cfzp030GoodLocalCredit p j (cfzp030ReadyGoodShape ε W p j k τ) ≤
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  simpa [cfzp030GoodLocalCredit, cfzp030ReadyGoodShape,
    cfzp030PrimePowerCriticalCarrier, mul_assoc] using
    (cfzp027PrimePowerBranchFreeTrigEvent_ge_readyPhaseCoreCredit
      hε hε2 W hp hj hsub hτ hτ4 hhit)

/-! ## Gate D: Bad local factorization -/

/-- The normalized local shape used by the automatic Bad envelope. -/
noncomputable def cfzp030BadLocalShape
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp029CenteredProfileDerivativeAbsBound ε W p j

/-- The automatic Bad debt is the common carrier times the Bad shape. -/
theorem cfzp029PrimePowerBadDebtEnvelope_eq_carrier_mul_badShape
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) :
    cfzp029PrimePowerBadDebtEnvelope ε W p j =
      cfzp030PrimePowerCriticalCarrier p j *
        cfzp030BadLocalShape ε W p j := by
  unfold cfzp029PrimePowerBadDebtEnvelope cfzp030PrimePowerCriticalCarrier
    cfzp030BadLocalShape
  ring

/-- The automatic Bad local shape is nonnegative on a safe cell. -/
theorem cfzp030BadLocalShape_nonneg
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 ≤ cfzp030BadLocalShape ε W p j := by
  exact cfzp029CenteredProfileDerivativeAbsBound_nonneg hε hε2 W hp hj

/-- The finite automatic Bad sum is also a carrier-weighted sum. -/
theorem cfzp029AutomaticBadDebtEnvelope_eq_carrier_sum
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (Bad : Finset (ℕ × ℕ)) :
    cfzp029AutomaticBadDebtEnvelope ε W Bad =
      ∑ pk ∈ Bad,
        cfzp030PrimePowerCriticalCarrier pk.1 (pk.2 + 1) *
          cfzp030BadLocalShape ε W pk.1 (pk.2 + 1) := by
  unfold cfzp029AutomaticBadDebtEnvelope
  apply Finset.sum_congr rfl
  intro pk hpk
  exact cfzp029PrimePowerBadDebtEnvelope_eq_carrier_mul_badShape
    ε W pk.1 (pk.2 + 1)

/-! ## Gate E: floor/ceiling endpoint comparison -/

/-- The Good right-endpoint floor is below the Bad left-endpoint ceiling. -/
theorem cfzp025CenteredDerivativePrefactorFloor_le_cfzp029Ceiling
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzp025CenteredDerivativePrefactorFloor ε W p j ≤
      cfzp029CenteredDerivativePrefactorCeiling ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hlt := cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j
  have ha : 0 ≤ cfzpModePhaseAbscissa W :=
    (cfzpModePhaseAbscissa_pos W).le
  have hexp : Real.exp (-(cfzpModePhaseAbscissa W) *
      cfzpPrimePowerPhaseMagnitudeRight ε p j) ≤
      Real.exp (-(cfzpModePhaseAbscissa W) *
        cfzpPrimePowerPhaseMagnitudeLeft ε p j) := by
    apply Real.exp_le_exp.mpr
    simpa [neg_mul] using
      (neg_le_neg (mul_le_mul_of_nonneg_left hlt.le ha))
  have hpow :
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j) ^ 3 ≤
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
    exact pow_le_pow_left₀ hmag.1.le hlt.le 3
  unfold cfzp025CenteredDerivativePrefactorFloor
    cfzp029CenteredDerivativePrefactorCeiling
  dsimp
  calc
    Real.exp (-(cfzpModePhaseAbscissa W) *
        cfzpPrimePowerPhaseMagnitudeRight ε p j) /
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 ≤
      Real.exp (-(cfzpModePhaseAbscissa W) *
        cfzpPrimePowerPhaseMagnitudeLeft ε p j) /
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) ^ 3 := by
      exact div_le_div_of_nonneg_right hexp (pow_pos hmag.2 3).le
    _ ≤ Real.exp (-(cfzpModePhaseAbscissa W) *
        cfzpPrimePowerPhaseMagnitudeLeft ε p j) /
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j) ^ 3 := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le
        (pow_pos hmag.1 3) hpow

/-! ## Gate F/G: finite carrier-weighted net balance -/

/-- The explicit finite Good-credit minus automatic Bad-debt balance. -/
noncomputable def cfzp030CertifiedNetBalance
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (cert : Cfzp024FiniteBlockCertificate ε W A B) : ℝ :=
  cfzp024CertifiedGoodCredit cert.Good cert.κ -
    cfzp029AutomaticBadDebtEnvelope ε W
      (cfzp024BadPrimePowerPairBlockSupport A B cert.Good)

/-- The net balance is the difference of two sums using one common carrier. -/
theorem cfzp030CertifiedNetBalance_eq_weightedGood_sub_weightedBad
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (cert : Cfzp024FiniteBlockCertificate ε W A B) :
    cfzp030CertifiedNetBalance W cert =
      (∑ pk ∈ cert.Good,
        cfzp030PrimePowerCriticalCarrier pk.1 (pk.2 + 1) * cert.κ pk) -
      (∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B cert.Good,
        cfzp030PrimePowerCriticalCarrier pk.1 (pk.2 + 1) *
          cfzp030BadLocalShape ε W pk.1 (pk.2 + 1)) := by
  unfold cfzp030CertifiedNetBalance
  rw [cfzp030CertifiedGoodCredit_eq_carrier_sum,
    cfzp029AutomaticBadDebtEnvelope_eq_carrier_sum]

/-- A ready-hit Good sum can be displayed with its explicit normalized shapes. -/
theorem cfzp030ReadyGoodCreditSum_eq_weightedReadyShapes
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (Good : Finset (ℕ × ℕ))
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ) :
    (∑ pk ∈ Good,
      cfzp030GoodLocalCredit pk.1 (pk.2 + 1)
        (cfzp030ReadyGoodShape ε W pk.1 (pk.2 + 1) (k pk) (τ pk))) =
      ∑ pk ∈ Good,
        cfzp030PrimePowerCriticalCarrier pk.1 (pk.2 + 1) *
          (cfzp025CenteredDerivativePrefactorFloor ε W pk.1 (pk.2 + 1) *
            cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W)
              (k pk) (τ pk)) := by
  apply Finset.sum_congr rfl
  intro pk hpk
  exact cfzp030ReadyGoodLocalCredit_eq ε W pk.1 (pk.2 + 1)
    (k pk) (τ pk)

/-- Pure algebra rewrites the old dominance shape into a net-balance bound. -/
theorem cfzp030_add_bad_le_good_add_iff_le_net_add
    {G Bad Good η : ℝ} :
    G + Bad ≤ Good + η ↔ G ≤ (Good - Bad) + η := by
  constructor <;> intro h <;> linarith

/-- The CFZP-024 dominance inequality implies the corresponding net bound. -/
theorem cfzp030CertifiedBlockDominance_implies_netBalance_bound
    {ε η : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (cert : Cfzp024FiniteBlockCertificate ε W A B)
    (hbad : cfzp024CertifiedBadDebtEnvelope
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good) cert.K =
      cfzp029AutomaticBadDebtEnvelope ε W
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good))
    (hdom : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp024CertifiedBadDebtEnvelope
          (cfzp024BadPrimePowerPairBlockSupport A B cert.Good) cert.K ≤
      cfzp024CertifiedGoodCredit cert.Good cert.κ + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp030CertifiedNetBalance W cert + η := by
  unfold cfzp030CertifiedNetBalance
  rw [← hbad]
  linarith

/-- An automatic net-balance dominance inequality reaches the block endpoint. -/
theorem cfzp030NetBalance_bound_implies_radialContactDeficit_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (cert : Cfzp024FiniteBlockCertificate ε W A B)
    (hbad : cfzp024CertifiedBadDebtEnvelope
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good) cert.K =
      cfzp029AutomaticBadDebtEnvelope ε W
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good))
    {η : ℝ}
    (hnet : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp030CertifiedNetBalance W cert + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  apply cfzp024CertifiedBlockDominance_radialContactDeficit_le
    hε hε2 W hAB
  refine ⟨cert, ?_⟩
  unfold cfzp030CertifiedNetBalance at hnet
  rw [← hbad] at hnet
  linarith

/-! ## Gate I: exact axis diagnostics -/

/-- The fixed-prime carrier at exponent one has its explicit closed form. -/
theorem cfzp030PrimePowerCriticalCarrier_one
    (p : ℕ) :
    cfzp030PrimePowerCriticalCarrier p 1 =
      2 * Real.log (p : ℝ) *
        Real.exp (-(1 : ℝ) / 2 * Real.log (p : ℝ)) := by
  simpa using cfzp030PrimePowerCriticalCarrier_eq_exp p 1

/-- The carrier formula records the exact exponent dependence, without an
asymptotic claim. -/
theorem cfzp030PrimePowerCriticalCarrier_explicit
    (p j : ℕ) :
    cfzp030PrimePowerCriticalCarrier p j =
      2 * Real.log (p : ℝ) *
        Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ)) :=
  cfzp030PrimePowerCriticalCarrier_eq_exp p j

/-! ## Firewall -/

/-- No weighted finite-balance or prime-axis mass provider is asserted. -/
inductive Cfzp030WeightedPrimePowerCreditDebtFactorizationGap : Prop
  | noIndependentWeightedFiniteBalanceProvider
  | noPrimeAxisWeightedMassProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider

end DkMath.RH.CFBRCProjection
