/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaExplicitSmoothMarginEscapeRadialAtBotAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaRadialEscapePrimeThresholdCrossingClosureAudit"

/-!
# CFZP-055: radial escape to exact prime-threshold crossing

This module transports the CFZP-054 cofinal radial-deficit escape through the
existing CFZP-018 finite equivalence.  Under the explicit PNT-ratio,
interior-strip, and subcritical-window hypotheses, it supplies the CFZP-017
exact crossing provider and the existing CFZP-018 consequences.  All crossing
and criticality conclusions remain finite-window statements; no global RH or
limit exchange is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gates A-B: fixed-epsilon exact crossing -/

/-- Radial escape at target zero gives an exact prime-threshold crossing beyond
every natural cutoff, for each positive phase below `log 2`. -/
theorem cfzp055_pntRatio_cofinal_exactPrimeThresholdCrossing
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
      cfzp017NormalizedPrimeThreshold epsilon W ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution epsilon W X := by
  intro N
  obtain ⟨c, n, _hc, hN, hdef⟩ :=
    cfzp054_exists_phase_pntRatio_cofinal_naturalCutoff_radialDeficit_le
      (eta := 0) hepsilon hepsilon2 W hstrip hsub hPNT N
  let X := cfzp040CarrierCellNaturalLeft W c n
  refine ⟨X, hN, ?_⟩
  exact (cfzp018PrimeThresholdCrossing_iff_radialContactDeficit_nonpos
    hepsilon W X).mpr hdef

/-- Packages the preceding `∀ N, ∃ X` witness property as the existing
`Filter.atTop` frequent exact-crossing interface. -/
theorem cfzp055_pntRatio_cfzp017CofinalPrimeThresholdCrossingAt
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp017CofinalPrimeThresholdCrossingAt epsilon W := by
  change ∃ᶠ X : ℕ in atTop,
    cfzp017NormalizedPrimeThreshold epsilon W ≤
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution epsilon W X
  rw [frequently_atTop]
  intro N
  obtain ⟨X, hNX, hcross⟩ :=
    cfzp055_pntRatio_cofinal_exactPrimeThresholdCrossing
      hepsilon hepsilon2 W hstrip hsub hPNT N
  exact ⟨X, hNX, hcross⟩

/-! ## Gates C-D: the existing approximate-reach and endpoint adapters -/

/-- Exact fixed-epsilon crossing implies the existing CFZP-018 approximate
reach contract; the latter is used only as a downstream weakening. -/
theorem cfzp055_pntRatio_cfzp018ApproximateReachAt
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp018CofinalPrimeThresholdApproximateReachAt epsilon W := by
  exact cfzp018CofinalPrimeThresholdApproximateReachAt_of_cfzp017
    hepsilon W
    (cfzp055_pntRatio_cfzp017CofinalPrimeThresholdCrossingAt
      hepsilon hepsilon2 W hstrip hsub hPNT)

/-- The fixed-epsilon arithmetic endpoint defect is nonpositive under the
same three explicit provider hypotheses. -/
theorem cfzp055_pntRatio_endpointArithmeticDefect_nonpos
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint epsilon W ≤ 0 := by
  exact (cfzp018CofinalPrimeThresholdApproximateReachAt_iff_endpoint_nonpos
    hepsilon W).mp
    (cfzp055_pntRatio_cfzp018ApproximateReachAt
      hepsilon hepsilon2 W hstrip hsub hPNT)

/-! ## Gates E-F: synchronization of the two cofinal parameters -/

/-- Positive epsilon below `log 2` holds eventually in the right-hand
neighborhood of zero. -/
theorem cfzp055_eventually_positive_lt_log_two :
    ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      0 < epsilon ∧ epsilon < Real.log 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlt : ∀ᶠ epsilon : ℝ in 𝓝 (0 : ℝ),
      epsilon < Real.log 2 := Iio_mem_nhds hlog
  have hlt' : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      epsilon < Real.log 2 := hlt.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlt', self_mem_nhdsWithin] with epsilon hεlt hεpos
  exact ⟨hεpos, hεlt⟩

/-- Supplies the doubly cofinal CFZP-017 exact crossing interface, conditional
on PNT ratio plus the explicit interior-strip and subcritical hypotheses. -/
theorem cfzp055_pntRatio_cfzp017DoublyCofinalPrimeThresholdCrossing
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp017DoublyCofinalPrimeThresholdCrossing W := by
  unfold Cfzp017DoublyCofinalPrimeThresholdCrossing
  have hev : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      0 < epsilon ∧ Cfzp017CofinalPrimeThresholdCrossingAt epsilon W := by
    filter_upwards [cfzp055_eventually_positive_lt_log_two] with epsilon hε
    exact ⟨hε.1,
      cfzp055_pntRatio_cfzp017CofinalPrimeThresholdCrossingAt
        hε.1 hε.2 W hstrip hsub hPNT⟩
  exact hev.frequently

/-! ## Gates G-I: downstream CFZP-018 and finite-window conclusions -/

/-- The exact CFZP-017 provider implies doubly cofinal CFZP-018 approximate
reach through the repository's existing hierarchy theorem. -/
theorem cfzp055_pntRatio_cfzp018DoublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Cfzp018DoublyCofinalPrimeThresholdApproximateReach W := by
  exact cfzp018DoublyCofinalPrimeThresholdApproximateReach_of_cfzp017
    W
    (cfzp055_pntRatio_cfzp017DoublyCofinalPrimeThresholdCrossing
      W hstrip hsub hPNT)

/-- The fixed second-moment defect is nonpositive under the conditional
CFZP-055 provider chain. -/
theorem cfzp055_pntRatio_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  exact cfzp018FixedDefect_nonpos_of_doublyCofinalPrimeThresholdApproximateReach
    W (cfzp055_pntRatio_cfzp018DoublyCofinalPrimeThresholdApproximateReach
      W hstrip hsub hPNT)

/-- Safe-window nonnegativity upgrades the conditional defect sign to
vanishing.  This is a finite-window statement, not a global RH theorem. -/
theorem cfzp055_pntRatio_fixedDefect_eq_zero
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  exact cfzp018FixedDefect_eq_zero_of_doublyCofinalPrimeThresholdApproximateReach
    W (cfzp055_pntRatio_cfzp018DoublyCofinalPrimeThresholdApproximateReach
      W hstrip hsub hPNT)

/-- Under the three explicit hypotheses, every zero in the selected finite
safe window lies on the critical line; no claim about all zeta zeros is made. -/
theorem cfzp055_pntRatio_finiteWindowZeros_critical
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ rho ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      rho.re = (1 : ℝ) / 2 := by
  exact cfzp017FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdCrossing
    W (cfzp055_pntRatio_cfzp017DoublyCofinalPrimeThresholdCrossing
      W hstrip hsub hPNT)

/-! ## Firewall -/

/-- Remaining CFZP-055 boundaries are provider boundaries rather than missing
adapters: PNT, automatic window hypotheses, and global finite-window
exhaustion remain outside this module. -/
inductive Cfzp055RadialEscapePrimeThresholdCrossingClosureGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSubcriticalAspectProvider
  | noGlobalFiniteWindowExhaustionProvider

end DkMath.RH.CFBRCProjection
