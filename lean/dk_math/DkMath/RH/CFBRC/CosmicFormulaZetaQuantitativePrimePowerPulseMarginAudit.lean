/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePulseBlockCompensationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePrimePowerPulseMarginAudit"

/-!
# CFZP-023: quantitative prime-power pulse margins

This module upgrades a conditional derivative sign on one centered
prime-power interval to an explicit profile-drop, event, and von-Mangoldt
pulse bound.  The derivative margin is kept as an explicit hypothesis: no
uniform margin provider, block dominance, phase equidistribution, limit
exchange, or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set

/-! ## Gate A: finite quantitative derivative inequalities -/

/-- A derivative bounded above by `-κ` forces a quantitative profile drop. -/
theorem cfzp023_derivative_drop_of_le_neg
    {f : ℝ → ℝ} {l r κ : ℝ}
    (hf : ContinuousOn f (Set.Icc l r))
    (hf' : DifferentiableOn ℝ f (interior (Set.Icc l r)))
    (_hκ : 0 ≤ κ)
    (hderiv : ∀ u ∈ Set.Ioo l r, deriv f u ≤ -κ)
    (hlr : l ≤ r) :
    κ * (r - l) ≤ f l - f r := by
  have h := (convex_Icc l r).image_sub_le_mul_sub_of_deriv_le
    hf hf' (fun u hu => by
      rw [interior_Icc] at hu
      exact hderiv u hu)
    l (left_mem_Icc.mpr hlr) r (right_mem_Icc.mpr hlr) hlr
  linarith

/-- A bounded absolute derivative gives a finite absolute profile envelope. -/
theorem cfzp023_abs_sub_le_of_deriv_abs_le
    {f : ℝ → ℝ} {l r K : ℝ}
    (hf : ContinuousOn f (Set.Icc l r))
    (hf' : DifferentiableOn ℝ f (interior (Set.Icc l r)))
    (_hK : 0 ≤ K)
    (hbound : ∀ u ∈ Set.Ioo l r, |deriv f u| ≤ K)
    (hlr : l ≤ r) :
    |f r - f l| ≤ K * (r - l) := by
  have hupper := (convex_Icc l r).image_sub_le_mul_sub_of_deriv_le
    hf hf' (fun u hu => by
      rw [interior_Icc] at hu
      exact le_trans (le_abs_self _) (hbound u hu))
    l (left_mem_Icc.mpr hlr) r (right_mem_Icc.mpr hlr) hlr
  have hlower := (convex_Icc l r).mul_sub_le_image_sub_of_le_deriv
    hf hf' (fun u hu => by
      rw [interior_Icc] at hu
      exact le_trans (neg_le_of_abs_le (hbound u hu)) (by linarith))
    l (left_mem_Icc.mpr hlr) r (right_mem_Icc.mpr hlr) hlr
  have habs : -K * (r - l) ≤ f r - f l ∧
      f r - f l ≤ K * (r - l) := by
    constructor
    · exact hlower
    · exact hupper
  rw [abs_le]
  constructor <;> linarith

/-! ## Gate B: exact centered width -/

/-- The centered prime-power magnitude interval has width exactly `2 * ε`. -/
theorem cfzp023PrimePowerPhaseMagnitude_width
    (ε : ℝ) (p j : ℕ) :
    cfzpPrimePowerPhaseMagnitudeRight ε p j -
        cfzpPrimePowerPhaseMagnitudeLeft ε p j = 2 * ε := by
  rw [cfzpPrimePowerPhaseMagnitudeRight,
    cfzpPrimePowerPhaseMagnitudeLeft]
  ring

/-! ## Gate C: explicit derivative-margin contracts -/

/-- A uniform negative derivative margin on one centered prime-power interval. -/
def Cfzp023CenteredProfileDerivativeDropMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) (κ : ℝ) : Prop :=
  ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
    deriv
      (fun x : ℝ =>
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T x) u ≤ -κ

/-- An absolute derivative envelope on one centered prime-power interval. -/
def Cfzp023CenteredProfileDerivativeAbsEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) (K : ℝ) : Prop :=
  ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
    |deriv
      (fun x : ℝ =>
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T x) u| ≤ K

private theorem cfzp023_profile_continuousOn
    {a T l r : ℝ} (hl : 0 < l) :
    ContinuousOn (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x)
      (Set.Icc l r) := by
  intro x hx
  exact (cfzpNegativeFrequencyBoundaryProfile_hasDerivAt
    (lt_of_lt_of_le hl hx.1).ne').continuousAt.continuousWithinAt

private theorem cfzp023_profile_differentiableOn
    {a T l r : ℝ} (hl : 0 < l) :
    DifferentiableOn ℝ
      (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x)
      (interior (Set.Icc l r)) := by
  intro x hx
  rw [interior_Icc] at hx
  exact (cfzpNegativeFrequencyBoundaryProfile_hasDerivAt
    (lt_trans hl hx.1).ne').differentiableAt.differentiableWithinAt

/-! ## Gate D: profile drop and absolute envelope -/

/-- The centered profile drop is at least `2 * ε * κ`. -/
theorem cfzp023CenteredProfile_drop_ge
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hmargin : Cfzp023CenteredProfileDerivativeDropMargin ε W p j κ) :
    2 * ε * κ ≤
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hlt := cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j
  have hdrop := cfzp023_derivative_drop_of_le_neg
    (cfzp023_profile_continuousOn hmag.1)
    (cfzp023_profile_differentiableOn hmag.1)
    hκ hmargin hlt.le
  rw [cfzp023PrimePowerPhaseMagnitude_width] at hdrop
  simpa [mul_comm, mul_left_comm, mul_assoc] using hdrop

/-- The centered profile difference has the absolute upper envelope
`2 * ε * K`. -/
theorem cfzp023CenteredProfile_abs_sub_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {K : ℝ} (hK : 0 ≤ K)
    (henv : Cfzp023CenteredProfileDerivativeAbsEnvelope ε W p j K) :
    |cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) -
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j)| ≤ 2 * ε * K := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hlt := cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j
  have hbound : ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      |deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T x) u| ≤ K := by
    intro u hu
    exact henv u hu
  have h := cfzp023_abs_sub_le_of_deriv_abs_le
    (cfzp023_profile_continuousOn hmag.1)
    (cfzp023_profile_differentiableOn hmag.1)
    hK hbound hlt.le
  rw [cfzp023PrimePowerPhaseMagnitude_width] at h
  simpa [abs_sub_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-! ## Gate E: event quantitative bounds -/

/-- A derivative-drop margin gives an explicit positive lower bound for the
branch-free prime-power event.  The factors `(2 * ε)⁻¹` and `2 * ε` cancel
exactly, leaving the smoothing-window-independent credit. -/
theorem cfzp023PrimePowerBranchFreeTrigEvent_ge_quantitativeCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hmargin : Cfzp023CenteredProfileDerivativeDropMargin ε W p j κ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * κ ≤
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hdrop := cfzp023CenteredProfile_drop_ge hε hε2 W hp hj hκ hmargin
  have hscale := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  have hmul := mul_le_mul_of_nonneg_left hdrop hscale.le
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  calc
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * κ =
        2 * Real.log (p : ℝ) *
          ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j)) *
          (2 * ε * κ) := by
            field_simp [ne_of_gt hε]
    _ ≤ 2 * Real.log (p : ℝ) *
          ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j)) *
          (cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
           cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeRight ε p j)) := hmul

/-- A strict derivative-drop margin yields a strictly positive event. -/
theorem cfzp023PrimePowerBranchFreeTrigEvent_pos_of_quantitativeCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {κ : ℝ} (hκ : 0 < κ)
    (hmargin : Cfzp023CenteredProfileDerivativeDropMargin ε W p j κ) :
    0 < cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hcredit := cfzp023PrimePowerBranchFreeTrigEvent_ge_quantitativeCredit
    hε hε2 W hp hj hκ.le hmargin
  have hlog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  have hscale : 0 < cfzpModeCriticalScale (p ^ j) :=
    cfzpModeCriticalScale_pos _
  have hcredit_pos :
      0 < 2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * κ :=
    mul_pos (mul_pos (mul_pos (by norm_num) hlog) hscale) hκ
  exact lt_of_lt_of_le hcredit_pos hcredit

/-- The zero-margin specialization records the compatibility with the
    existing sign-level interface: a nonpositive derivative on the centered
    interval gives a nonnegative event, without asserting a strict margin. -/
theorem cfzp023PrimePowerBranchFreeTrigEvent_nonneg_of_zero_margin
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hmargin : Cfzp023CenteredProfileDerivativeDropMargin ε W p j 0) :
    0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  simpa using cfzp023PrimePowerBranchFreeTrigEvent_ge_quantitativeCredit
    hε hε2 W hp hj (by norm_num) hmargin

/-! ## Gate F: event absolute upper envelope -/

/-- An absolute derivative envelope gives an explicit event magnitude bound. -/
theorem cfzp023PrimePowerBranchFreeTrigEvent_abs_le_quantitativeEnvelope
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {K : ℝ} (hK : 0 ≤ K)
    (henv : Cfzp023CenteredProfileDerivativeAbsEnvelope ε W p j K) :
    |cfzpPrimePowerBranchFreeTrigEvent ε W p j| ≤
      2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * K := by
  have hdiff := cfzp023CenteredProfile_abs_sub_le hε hε2 W hp hj hK henv
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  rw [abs_mul]
  have hscale := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  have hdiff' :
      |cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
        cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeRight ε p j)| ≤ 2 * ε * K := by
    simpa [abs_sub_comm] using hdiff
  have hmul := mul_le_mul_of_nonneg_left hdiff' hscale.le
  rw [abs_of_pos hscale]
  calc
    cfzpPrimePowerEventPositiveScale ε p j *
        |cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
          cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeRight ε p j)| ≤
        cfzpPrimePowerEventPositiveScale ε p j * (2 * ε * K) := hmul
    _ = 2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * K := by
      unfold cfzpPrimePowerEventPositiveScale
      field_simp [ne_of_gt hε]

/-! ## Gate G/H: mass, debt, and pulse adapters -/

/-- The quantitative event credit is paid by canonical positive event mass. -/
theorem cfzp023PrimePowerEventPositiveMass_ge_quantitativeCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hmargin : Cfzp023CenteredProfileDerivativeDropMargin ε W p j κ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * κ ≤
      cfzp019PrimePowerEventPositiveMass ε W p j := by
  apply le_trans
    (cfzp023PrimePowerBranchFreeTrigEvent_ge_quantitativeCredit
      hε hε2 W hp hj hκ hmargin)
  exact le_max_left _ _

/-- The event magnitude envelope pays an upper bound on canonical negative
event debt. -/
theorem cfzp023PrimePowerEventNegativeDebt_le_quantitativeEnvelope
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {K : ℝ} (hK : 0 ≤ K)
    (henv : Cfzp023CenteredProfileDerivativeAbsEnvelope ε W p j K) :
    cfzp019PrimePowerEventNegativeDebt ε W p j ≤
      2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * K := by
  have habs := cfzp023PrimePowerBranchFreeTrigEvent_abs_le_quantitativeEnvelope
    hε hε2 W hp hj hK henv
  unfold cfzp019PrimePowerEventNegativeDebt
  apply max_le
  · exact (neg_le_abs _).trans habs
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (by
        apply Real.log_pos
        exact_mod_cast hp.one_lt)))
        (cfzpModeCriticalScale_pos (p ^ j)).le)
      hK

/-- The event bounds transport to the von-Mangoldt pulse at a prime power. -/
theorem cfzp023VonMangoldtPulse_ge_quantitativeCredit_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hmargin : Cfzp023CenteredProfileDerivativeDropMargin ε W p j κ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * κ ≤
      cfzp021VonMangoldtPulse ε W n := by
  rw [hn, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzp023PrimePowerBranchFreeTrigEvent_ge_quantitativeCredit
    hε hε2 W hp hj hκ hmargin

/-- The absolute event envelope transports unchanged to the prime-power
    von-Mangoldt pulse. -/
theorem cfzp023VonMangoldtPulse_abs_le_quantitativeEnvelope_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j)
    {K : ℝ} (hK : 0 ≤ K)
    (henv : Cfzp023CenteredProfileDerivativeAbsEnvelope ε W p j K) :
    |cfzp021VonMangoldtPulse ε W n| ≤
      2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * K := by
  rw [hn, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzp023PrimePowerBranchFreeTrigEvent_abs_le_quantitativeEnvelope
    hε hε2 W hp hj hK henv

/-! ## Gate J: explicit provider gap -/

/-- The derivative-margin machinery does not provide a uniform prime-power
margin or block-dominance provider. -/
inductive Cfzp023QuantitativePrimePowerPulseMarginGap : Prop
  | noIndependentUniformPrimePowerDerivativeMarginProvider

end DkMath.RH.CFBRCProjection
