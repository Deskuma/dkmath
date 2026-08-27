/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaRadialMarginPrimeThresholdDecompositionAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCofinalRadialContactAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffContactBaselineAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeThresholdApproximateReachFrontierAudit"

/-!
# CFZP-018: prime-threshold approximate-reach frontier

This module identifies the CFZP-017 prime threshold with the existing CS24
correction source and zero-cutoff radial deficit.  It then weakens exact
threshold crossing to arbitrary-slack cofinal reach and identifies that
interface with the existing CS22 cofinal radial contact contract.  No
approximate-reach provider, phase-cell provider, joint limit, or RH statement
is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gate A: threshold and correction source -/

/-- The normalized prime threshold is the fixed radial observable minus the
three X-independent correction terms. -/
theorem cfzp018NormalizedPrimeThreshold_eq_fixed_sub_correction
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    cfzp017NormalizedPrimeThreshold ε W =
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W := by
  unfold cfzp017NormalizedPrimeThreshold
    pascalCenteredXiPrimeSideIndependentCorrectionSourceReal
  ring

/-! ## Gate B: zero-cutoff normalization -/

/-- Multiplying the normalized prime threshold by pi gives the existing
zero-cutoff radial contact deficit. -/
theorem cfzp018_pi_mul_normalizedPrimeThreshold_eq_zeroCutoffRadialDeficit
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Real.pi * cfzp017NormalizedPrimeThreshold ε W =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  have hbase :=
    pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
      hε W 0
  have hzero := cfzpIndependentCompleteSourceReal_zeroCutoff_eq_correctionSourceReal
    hε W
  rw [hbase, hzero]
  unfold cfzp017NormalizedPrimeThreshold
    pascalCenteredXiPrimeSideIndependentCorrectionSourceReal
  ring

/-! ## Gate C: margin and finite radial-deficit coordinates -/

/-- The CFZP-015 whole-shifted margin is negative four times the finite
radial contact deficit. -/
theorem cfzp018WholeShiftedRadialMargin_eq_neg_four_mul_radialContactDeficit
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp015WholeShiftedRadialMargin ε W X =
      -4 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have hmargin :=
    cfzp015WholeShiftedRadialMargin_eq_neg_four_mul_pi_mul_defect hε W X
  have hdeficit :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_defect
      hε W X
  rw [hmargin, hdeficit]
  ring

/-- Nonnegative whole-shifted margin is equivalent to a nonpositive finite
radial contact deficit. -/
theorem cfzp018WholeShiftedRadialMargin_nonneg_iff_radialContactDeficit_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 := by
  rw [cfzp018WholeShiftedRadialMargin_eq_neg_four_mul_radialContactDeficit hε W X]
  constructor <;> intro h <;> linarith

/-- The CFZP-017 exact prime-threshold crossing is the same finite
zero-crossing observable as the radial contact deficit. -/
theorem cfzp018PrimeThresholdCrossing_iff_radialContactDeficit_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp017NormalizedPrimeThreshold ε W ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 := by
  rw [← cfzp017WholeShiftedRadialMargin_nonneg_iff_primeThreshold_le hε W X,
    cfzp018WholeShiftedRadialMargin_nonneg_iff_radialContactDeficit_nonpos hε W X]

/-- The finite deficit is the pi-scaled difference between the threshold and
the normalized prime contribution. -/
theorem cfzp018RadialContactDeficit_eq_pi_mul_threshold_sub_prime
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      Real.pi *
        (cfzp017NormalizedPrimeThreshold ε W -
          pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X) := by
  have hmargin :=
    cfzp017WholeShiftedRadialMargin_eq_four_pi_mul_primeThresholdExcess hε W X
  have hneg :=
    cfzp018WholeShiftedRadialMargin_eq_neg_four_mul_radialContactDeficit hε W X
  rw [hneg] at hmargin
  linarith

/-! ## Gate D: aggregate interaction reach -/

/-- Exact prime-threshold crossing is equivalently zero-cutoff deficit below
the aggregate interaction energy. -/
theorem cfzp018PrimeThresholdCrossing_iff_zeroCutoffInteractionReach
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp017NormalizedPrimeThreshold ε W ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hthreshold :=
    cfzp018_pi_mul_normalizedPrimeThreshold_eq_zeroCutoffRadialDeficit hε W
  have hprime :=
    cfzp017WholeShiftedRadialMargin_nonneg_iff_aggregateInteraction_ge hε W X
  have hcross :=
    cfzp017WholeShiftedRadialMargin_nonneg_iff_primeThreshold_le hε W X
  constructor
  · intro h
    have hm := hcross.mpr h
    have hi := hprime.mp hm
    rw [hthreshold] at hi
    exact hi
  · intro h
    apply hcross.mp
    apply hprime.mpr
    rw [hthreshold]
    exact h

/-! ## Gate E: arbitrary-slack threshold reach -/

/-- Every positive normalized slack is reached at arbitrarily late finite
cutoffs.  This is weaker than frequent exact threshold crossing. -/
def Cfzp018CofinalPrimeThresholdApproximateReachAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    cfzp017NormalizedPrimeThreshold ε W - δ ≤
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X

/-- The finite radial deficit is pi times the normalized threshold slack. -/
theorem cfzp018CofinalPrimeThresholdApproximateReachAt_iff_csf
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp018CofinalPrimeThresholdApproximateReachAt ε W ↔
      PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W := by
  constructor
  · intro hreach η hη N
    have hδ : 0 < η / Real.pi := div_pos hη Real.pi_pos
    rcases hreach (η / Real.pi) hδ N with ⟨X, hNX, happrox⟩
    refine ⟨X, hNX, ?_⟩
    have hdef :=
      cfzp018RadialContactDeficit_eq_pi_mul_threshold_sub_prime hε W X
    have hle :
        cfzp017NormalizedPrimeThreshold ε W -
            pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X
          ≤ η / Real.pi := by
      linarith
    rw [hdef]
    calc
      Real.pi *
          (cfzp017NormalizedPrimeThreshold ε W -
            pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X) ≤
          Real.pi * (η / Real.pi) :=
        mul_le_mul_of_nonneg_left hle Real.pi_pos.le
      _ = 0 + η := by
        field_simp [Real.pi_ne_zero]
        ring
  · intro hcontact δ hδ N
    have hη : 0 < Real.pi * δ := mul_pos Real.pi_pos hδ
    rcases hcontact (Real.pi * δ) hη N with ⟨X, hNX, hcontactX⟩
    refine ⟨X, hNX, ?_⟩
    have hdef :=
      cfzp018RadialContactDeficit_eq_pi_mul_threshold_sub_prime hε W X
    have hscaled :
        Real.pi *
            (cfzp017NormalizedPrimeThreshold ε W -
              pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X)
          ≤ Real.pi * δ := by
      rw [← hdef]
      simpa using hcontactX
    have hle :
        cfzp017NormalizedPrimeThreshold ε W -
            pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X
          ≤ δ :=
      le_of_mul_le_mul_left hscaled Real.pi_pos
    linarith

/-- Arbitrary-slack threshold reach is equivalent to nonpositive endpoint
arithmetic defect at fixed positive epsilon. -/
theorem cfzp018CofinalPrimeThresholdApproximateReachAt_iff_endpoint_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp018CofinalPrimeThresholdApproximateReachAt ε W ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0 := by
  rw [cfzp018CofinalPrimeThresholdApproximateReachAt_iff_csf hε W,
    pascalCenteredXiPrimeSideCofinalRadialContactZeroAt_iff_endpoint_nonpos hε W]

/-! ## Gate G: exact crossing versus approximate reach -/

/-- Exact cofinal threshold crossing implies arbitrary-slack cofinal reach. -/
theorem cfzp018CofinalPrimeThresholdApproximateReachAt_of_cfzp017
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hcross : Cfzp017CofinalPrimeThresholdCrossingAt ε W) :
    Cfzp018CofinalPrimeThresholdApproximateReachAt ε W := by
  intro δ hδ N
  have hN : ∀ᶠ X : ℕ in atTop, N ≤ X := eventually_ge_atTop N
  rcases (hcross.and_eventually hN).exists with ⟨X, hX, hNX⟩
  refine ⟨X, hNX, ?_⟩
  linarith

/-- A pointwise positive slack relation does not imply exact threshold
crossing; this is only a local real-number firewall. -/
theorem cfzp018ApproximateSlack_does_not_imply_exactCrossing :
    ∃ P T δ : ℝ, 0 < δ ∧ T - δ ≤ P ∧ ¬ T ≤ P := by
  refine ⟨0, 1, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-! ## Gate H: doubly cofinal approximate reach -/

/-- Arbitrary-slack prime-threshold reach is available at cofinally many
positive smoothing parameters. -/
def Cfzp018DoublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ Cfzp018CofinalPrimeThresholdApproximateReachAt ε W

private theorem nonpos_of_tendsto_of_frequently_nonpos
    {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (hlim : Tendsto f l (nhds L))
    (hfreq : ∃ᶠ x in l, f x ≤ 0) :
    L ≤ 0 := by
  by_contra hL
  have hLpos : 0 < L := lt_of_not_ge hL
  have hev : ∀ᶠ x in l, 0 < f x := hlim.eventually (Ioi_mem_nhds hLpos)
  exact hfreq (hev.mono fun _ hx => not_le_of_gt hx)

/-- The doubly cofinal approximate-reach provider forces finite-window
criticality, conditionally on its existence. -/
theorem cfzp018FixedDefect_nonpos_of_doublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow)
    (hreach : Cfzp018DoublyCofinalPrimeThresholdApproximateReach W) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  apply nonpos_of_tendsto_of_frequently_nonpos
    (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon W)
  exact hreach.mono fun ε hε =>
    (cfzp018CofinalPrimeThresholdApproximateReachAt_iff_endpoint_nonpos
      hε.1 W).mp hε.2

/-- Safe-radius nonnegativity upgrades the conditional fixed sign to
vanishing on the finite window. -/
theorem cfzp018FixedDefect_eq_zero_of_doublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow)
    (hreach : Cfzp018DoublyCofinalPrimeThresholdApproximateReach W) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  apply le_antisymm
  · exact cfzp018FixedDefect_nonpos_of_doublyCofinalPrimeThresholdApproximateReach
      W hreach
  · exact pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg W.circle_safe

/-- The conditional approximate-reach provider forces finite-window zeros onto
the critical line. -/
theorem cfzp018FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow)
    (hreach : Cfzp018DoublyCofinalPrimeThresholdApproximateReach W) :
    ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      ρ.re = (1 : ℝ) / 2 := by
  apply (pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
    W.circle_safe).mp
  exact cfzp018FixedDefect_eq_zero_of_doublyCofinalPrimeThresholdApproximateReach
    W hreach

/-! ## Gate I: provider hierarchy -/

/-- The stronger CFZP-017 doubly cofinal exact crossing provider implies the
weaker CFZP-018 doubly cofinal approximate-reach provider. -/
theorem cfzp018DoublyCofinalPrimeThresholdApproximateReach_of_cfzp017
    (W : PascalCenteredXiResidueTransportWindow)
    (hcross : Cfzp017DoublyCofinalPrimeThresholdCrossing W) :
    Cfzp018DoublyCofinalPrimeThresholdApproximateReach W := by
  exact hcross.mono fun ε hε =>
    ⟨hε.1, cfzp018CofinalPrimeThresholdApproximateReachAt_of_cfzp017
      hε.1 W hε.2⟩

/-! ## Gate J: the sharpened approximate-reach frontier -/

/-- An independent doubly cofinal approximate-reach provider remains open. -/
inductive Cfzp018PrimeThresholdApproximateReachGap : Prop
  | noIndependentDoublyCofinalPrimeThresholdApproximateReachProvider

end DkMath.RH.CFBRCProjection
