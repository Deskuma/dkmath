/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFiniteSmoothAbelReadinessRadialEighthDescentAudit
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaExplicitSmoothMarginEscapeRadialAtBotAudit"

/-!
# CFZP-054: explicit smooth-margin escape and radial `atBot`

The positive exponential carrier margin eventually dominates the fixed linear
cell descent.  The resulting `atBot` statement is obtained by finite
induction on a tail; no infinite margin sum or limit exchange is used here.
The arithmetic input remains the explicit CFZP-051 PNT-ratio provider.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Filter

/-! ## Gate A: exponential growth beats the linear denominator -/

/-- A positive exponential rate makes `exp (beta * U) / U` tend to `+∞`.

This is a pure real-analysis fact.  It does not use any prime-counting or
prime-sum statement.
-/
theorem cfzp054_exp_mul_inv_tendsto_atTop
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun U : ℝ => Real.exp (beta * U) / U)
      Filter.atTop Filter.atTop := by
  have hscale : Filter.Tendsto (fun U : ℝ => beta * U)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 ?_
    intro K
    refine ⟨K / beta, ?_⟩
    intro U hU
    calc
      K = beta * (K / beta) := by field_simp [hbeta.ne']
      _ ≤ beta * U := mul_le_mul_of_nonneg_left hU hbeta.le
  have hbase :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hsmall : Filter.Tendsto
      (fun U : ℝ => U * Real.exp (-(beta * U)))
      Filter.atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ => beta⁻¹) Filter.atTop (nhds beta⁻¹)).mul hbase
    convert hmul using 1
    · funext U
      simp [pow_one]
      field_simp [hbeta.ne']
    · simp
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro K
  by_cases hK : K ≤ 0
  · exact ⟨0, fun U _ => le_trans hK (by positivity)⟩
  · have hKpos : 0 < K := lt_of_not_ge hK
    have hscaled :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ => K) Filter.atTop (nhds K)).mul hsmall
    have hsmallOne : ∀ᶠ U : ℝ in Filter.atTop,
        K * (U * Real.exp (-(beta * U))) < 1 :=
      hscaled.eventually (Iio_mem_nhds (by norm_num))
    have hUpos : ∀ᶠ U : ℝ in Filter.atTop, 0 < U :=
      eventually_atTop.2 ⟨1, by intro U hU; linarith⟩
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 (hsmallOne.and hUpos)
    refine ⟨U₀, ?_⟩
    intro U hU
    have hineq := hU₀ U hU
    have hposU : 0 < U := hineq.2
    have hexp : 0 < Real.exp (beta * U) := Real.exp_pos _
    have hmul : K * U * Real.exp (-(beta * U)) < 1 := by
      simpa [mul_assoc] using hineq.1
    have hmul' : K * U < Real.exp (beta * U) := by
      calc
        K * U = (K * U * Real.exp (-(beta * U))) * Real.exp (beta * U) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
        _ < 1 * Real.exp (beta * U) := mul_lt_mul_of_pos_right hmul hexp
        _ = Real.exp (beta * U) := one_mul _
    exact (le_div_iff₀ hposU).2 (le_of_lt hmul')

/-! ## Gates B-C: the explicit margin escapes and supplies fixed floors -/

/-- The explicit smooth margin tends to `+∞` along every positive late phase.
-/
theorem cfzp054ExplicitSmoothMargin_tendsto_atTop
    {epsilon : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    Filter.Tendsto
      (fun n : ℕ => cfzp044ExplicitSmoothMargin epsilon W c n)
      Filter.atTop Filter.atTop := by
  have hbeta : 0 < cfzp039PrimeAxisGrowthExponent W :=
    cfzp039PrimeAxisGrowthExponent_pos W hstrip
  have hratio := cfzp054_exp_mul_inv_tendsto_atTop hbeta
  have hleft := cfzp047CarrierCellLeft_tendsto_atTop W c
  have hratio' := hratio.comp hleft
  have hscale : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c / 4 :=
    div_pos hM (by norm_num)
  have hmargin := Tendsto.const_mul_atTop hscale hratio'
  have hpos : ∀ᶠ n : ℕ in Filter.atTop,
      0 < cfzp039CarrierCellLeft W c n :=
    (hleft.eventually_ge_atTop 1).mono fun _ h => lt_of_lt_of_le
      (by norm_num) h
  refine hmargin.congr' ?_
  filter_upwards [hpos] with n hn
  simp only [Function.comp_apply]
  unfold cfzp044ExplicitSmoothMargin
  field_simp [ne_of_gt hn]

/-- Every fixed real floor is eventually below the explicit smooth margin. -/
theorem cfzp054ExplicitSmoothMargin_eventually_ge
    {epsilon K : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      K ≤ cfzp044ExplicitSmoothMargin epsilon W c n := by
  exact (cfzp054ExplicitSmoothMargin_tendsto_atTop W hstrip c hM).eventually_ge_atTop K

/-- The convenient unit-descent floor `Margin ≥ 8` is eventual. -/
theorem cfzp054ExplicitSmoothMargin_eventually_ge_eight
    {epsilon : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      8 ≤ cfzp044ExplicitSmoothMargin epsilon W c n := by
  exact cfzp054ExplicitSmoothMargin_eventually_ge W hstrip c hM

/-! ## Gates D-E: unit recurrence and finite linear descent -/

/-- Under the explicit PNT-ratio provider, the eighth recurrence becomes a
unit radial descent after the margin reaches eight. -/
theorem cfzp054_pntRatio_eventually_leftRadialDeficit_succ_le_sub_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c (n + 1) ≤
        cfzp053LeftRadialDeficit epsilon W c n - 1 := by
  have hrec := cfzp053_pntRatio_eventually_leftRadialDeficit_succ_le_sub_eighthMargin
    hepsilon hepsilon2 W hstrip hsub c hM hPNT
  have h8 := cfzp054ExplicitSmoothMargin_eventually_ge (K := 8) W hstrip c hM
  filter_upwards [hrec, h8] with n hn hmargin
  linarith

/-- A finite tail of the unit recurrence descends linearly by its length. -/
theorem cfzp054_leftRadialDeficit_iterate_le_sub_nat
    {epsilon : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (N m : ℕ)
    (hstep : ∀ k : ℕ, N ≤ k →
      cfzp053LeftRadialDeficit epsilon W c (k + 1) ≤
        cfzp053LeftRadialDeficit epsilon W c k - 1) :
    cfzp053LeftRadialDeficit epsilon W c (N + m) ≤
      cfzp053LeftRadialDeficit epsilon W c N - (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrec := hstep (N + m) (by omega)
    calc
      cfzp053LeftRadialDeficit epsilon W c (N + (m + 1)) =
          cfzp053LeftRadialDeficit epsilon W c ((N + m) + 1) := by
            rw [Nat.add_assoc]
      _ ≤ cfzp053LeftRadialDeficit epsilon W c (N + m) - 1 := hrec
      _ ≤ (cfzp053LeftRadialDeficit epsilon W c N - (m : ℝ)) - 1 :=
        sub_le_sub_right ih _
      _ = cfzp053LeftRadialDeficit epsilon W c N - ((m + 1 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
        ring

/-! ## Gate F: radial deficit escapes to `-∞` by finite tails -/

/-- The left radial deficit tends to `-∞` under the supplied PNT ratio and
the explicit interior/subcritical window hypotheses. -/
theorem cfzp054_pntRatio_leftRadialDeficit_tendsto_atBot
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Filter.Tendsto
      (cfzp053LeftRadialDeficit epsilon W c)
      Filter.atTop Filter.atBot := by
  have hev := cfzp054_pntRatio_eventually_leftRadialDeficit_succ_le_sub_one
    hepsilon hepsilon2 W hstrip hsub c hM hPNT
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine Filter.tendsto_atTop_atBot.2 ?_
  intro eta
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge
    (cfzp053LeftRadialDeficit epsilon W c N - eta)
  have htail : cfzp053LeftRadialDeficit epsilon W c N - (m₀ : ℝ) ≤ eta := by
    have hm₀' : cfzp053LeftRadialDeficit epsilon W c N - eta ≤ (m₀ : ℝ) :=
      hm₀
    linarith
  refine ⟨N + m₀, ?_⟩
  intro n hn
  have hNn : N ≤ n := le_trans (Nat.le_add_right N m₀) hn
  let m := n - N
  have hNm : N + m = n := by
    dsimp [m]
    omega
  have hm₀m : m₀ ≤ m := by
    dsimp [m]
    omega
  have hlinear := cfzp054_leftRadialDeficit_iterate_le_sub_nat
    W c N m (fun k hk => hN k (le_trans hk (by omega)))
  rw [hNm] at hlinear
  have hcast : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm₀m
  linarith

/-! ## Gate G: fixed radial targets and cofinal cell indices -/

/-- Every fixed radial target is eventually attained by the left-cell deficit. -/
theorem cfzp054_pntRatio_eventually_leftRadialDeficit_le
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c n ≤ eta := by
  exact (cfzp054_pntRatio_leftRadialDeficit_tendsto_atBot
    hepsilon hepsilon2 W hstrip hsub c hM hPNT).eventually
    (Iic_mem_atBot eta)

/-- A left-cell index can be chosen beyond any prescribed index while meeting
an arbitrary radial target. -/
theorem cfzp054_pntRatio_exists_leftRadialDeficit_le
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      cfzp053LeftRadialDeficit epsilon W c n ≤ eta := by
  have hEv : ∀ᶠ n : ℕ in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c n ≤ eta :=
    cfzp054_pntRatio_eventually_leftRadialDeficit_le
      hepsilon hepsilon2 W hstrip hsub c hM hPNT
  obtain ⟨N', hN'⟩ := eventually_atTop.1 hEv
  refine ⟨max N N', le_max_left _ _, hN' _ (le_max_right _ _)⟩

/-! ## Gate H: natural carrier cutoffs are cofinal -/

/-- The natural left cutoffs obtained by flooring the exponential endpoints
tend to `+∞`. -/
theorem cfzp054CarrierCellNaturalLeft_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => cfzp040CarrierCellNaturalLeft W c n)
      Filter.atTop Filter.atTop := by
  have hleft := cfzp047CarrierCellLeft_tendsto_atTop W c
  have hexp := (Real.tendsto_exp_atTop.comp hleft)
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).comp hexp
  simpa [cfzp040CarrierCellNaturalLeft, cfzp040CarrierCellExpLeft,
    Function.comp_def] using hfloor

/-! ## Gate I: cofinal natural-cutoff radial escape -/

/-- Beyond every natural cutoff floor, a natural carrier endpoint realizes any
prescribed radial deficit target. -/
theorem cfzp054_pntRatio_cofinal_naturalCutoff_radialDeficit_le
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (N : ℕ) :
    ∃ n : ℕ,
      N ≤ cfzp040CarrierCellNaturalLeft W c n ∧
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
          (cfzp040CarrierCellNaturalLeft W c n) ≤ eta := by
  have hNat :=
    (cfzp054CarrierCellNaturalLeft_tendsto_atTop W c).eventually_ge_atTop N
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hNat
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1
    (cfzp054_pntRatio_eventually_leftRadialDeficit_le
      hepsilon hepsilon2 W hstrip hsub c hM hPNT)
  let n := max N₀ M₁
  refine ⟨n, ?_, ?_⟩
  · exact hN₀ n (le_max_left _ _)
  · exact hM₁ n (le_max_right _ _)

/-! ## Optional positive-phase wrapper -/

/-- Positive phase and the cofinal natural-cutoff radial escape can be chosen
together whenever the existing CFZP-039 phase-existence theorem applies. -/
theorem cfzp054_exists_phase_pntRatio_cofinal_naturalCutoff_radialDeficit_le
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (N : ℕ) :
    ∃ c : ℝ, ∃ n : ℕ,
      0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c ∧
      N ≤ cfzp040CarrierCellNaturalLeft W c n ∧
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
          (cfzp040CarrierCellNaturalLeft W c n) ≤ eta := by
  obtain ⟨c, hc⟩ := cfzp039ExponentialCarrierPeriodTransform_exists_pos
    hepsilon W hstrip
  obtain ⟨n, hnN, hnη⟩ := cfzp054_pntRatio_cofinal_naturalCutoff_radialDeficit_le
    hepsilon hepsilon2 W hstrip hsub c hc hPNT N
  exact ⟨c, n, hc, hnN, hnη⟩

/-! ## Firewall -/

/-- Remaining CFZP-054 boundaries are explicit inputs rather than automatic
providers: arithmetic PNT, the interior strip, the subcritical window, and
the next CFZP-018 adapter remain outside this module. -/
inductive Cfzp054ExplicitSmoothMarginEscapeRadialAtBotGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSubcriticalAspectProvider
  | noApproximateReachAdapter

end DkMath.RH.CFBRCProjection
