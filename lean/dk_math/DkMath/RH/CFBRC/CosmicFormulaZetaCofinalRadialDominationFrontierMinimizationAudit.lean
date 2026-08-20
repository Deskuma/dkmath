/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaArithmeticRadialDominationMarginFrontierAudit
import DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCofinalRadialDominationFrontierMinimizationAudit"

/-!
# CFZP-016: cofinal radial-domination frontier minimization

This module weakens the CFZP-015 eventual radial-domination provider to a
strictly weaker sufficient interface for the current ordered-limit route.
Frequently nonnegative finite margins force a nonnegative endpoint margin at
fixed positive epsilon, and frequently nonnegative endpoint margins along
the positive-side neighborhood of zero force a nonnegative fixed margin.  No
provider for either cofinal condition is constructed, and no joint limit,
limit exchange, contour relocation, or unconditional RH statement is
introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gate A: endpoint and fixed radial margins -/

/-- The endpoint of the CFZP-015 whole-shifted radial margin. -/
noncomputable def cfzp016EndpointRadialMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  -4 * Real.pi *
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W

/-- The fixed-Xi limit of the CFZP-016 radial margin. -/
noncomputable def cfzp016FixedRadialMargin
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  -4 * Real.pi *
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R

/-- At fixed positive epsilon, finite whole-shifted margins converge to the
endpoint margin by the existing arithmetic-defect convergence theorem. -/
theorem tendsto_cfzp016WholeShiftedRadialMargin
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X : ℕ => cfzp015WholeShiftedRadialMargin ε W X)
      atTop
      (nhds (cfzp016EndpointRadialMargin ε W)) := by
  have hconst : Tendsto (fun _ : ℕ => -4 * Real.pi) atTop
      (nhds (-4 * Real.pi)) := tendsto_const_nhds
  have hdef := tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    hε W
  have hmul := hconst.mul hdef
  convert hmul using 1
  · funext X
    exact cfzp015WholeShiftedRadialMargin_eq_neg_four_mul_pi_mul_defect hε W X
  · rfl

/-- Endpoint margins converge to the fixed margin along the positive-side
neighborhood of zero. -/
theorem tendsto_cfzp016EndpointRadialMargin_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => cfzp016EndpointRadialMargin ε W)
      (𝓝[>] 0)
      (nhds (cfzp016FixedRadialMargin W)) := by
  have hconst : Tendsto (fun _ : ℝ => -4 * Real.pi) (𝓝[>] 0)
      (nhds (-4 * Real.pi)) := tendsto_const_nhds
  have hdef := tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon W
  have hmul := hconst.mul hdef
  convert hmul using 1 <;> rfl

/-- The endpoint margin is nonnegative exactly when the endpoint defect is
nonpositive. -/
theorem cfzp016EndpointRadialMargin_nonneg_iff_defectEndpoint_nonpos
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp016EndpointRadialMargin ε W ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0 := by
  unfold cfzp016EndpointRadialMargin
  have hpi : 0 < (4 : ℝ) * Real.pi := by positivity
  constructor
  · intro h
    have hprod : (4 * Real.pi) *
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0 := by
      linarith
    exact nonpos_of_mul_nonpos_right hprod hpi
  · intro h
    have hprod : (4 * Real.pi) *
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpi.le h
    linarith

/-- The fixed margin is nonnegative exactly when the fixed defect is
nonpositive. -/
theorem cfzp016FixedRadialMargin_nonneg_iff_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp016FixedRadialMargin W ↔
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  unfold cfzp016FixedRadialMargin
  have hpi : 0 < (4 : ℝ) * Real.pi := by positivity
  constructor
  · intro h
    have hprod : (4 * Real.pi) *
        pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
      linarith
    exact nonpos_of_mul_nonpos_right hprod hpi
  · intro h
    have hprod : (4 * Real.pi) *
        pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpi.le h
    linarith

/-! ## Gate B: frequent nonnegative limits -/

/-- A real limit cannot be negative when its values are frequently
nonnegative. -/
private theorem nonneg_of_tendsto_of_frequently_nonneg
    {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (hlim : Tendsto f l (nhds L))
    (hfreq : ∃ᶠ x in l, 0 ≤ f x) :
    0 ≤ L := by
  by_contra hL
  have hLneg : L < 0 := lt_of_not_ge hL
  have hev : ∀ᶠ x in l, f x < 0 := hlim.eventually (Iio_mem_nhds hLneg)
  exact hfreq (hev.mono fun _ hx => not_le_of_gt hx)

/-! ## Gate C: fixed-epsilon cofinal cutoff domination -/

/-- Cofinally many finite cutoffs have a nonnegative CFZP-015 margin at a
fixed epsilon. -/
def Cfzp016CofinalCutoffRadialDominationAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ X : ℕ in atTop,
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X

/-- Fixed-epsilon cofinal radial domination forces a nonnegative endpoint
margin. -/
theorem cfzp016EndpointRadialMargin_nonneg_of_cofinalCutoffRadialDominationAt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp016CofinalCutoffRadialDominationAt ε W) :
    0 ≤ cfzp016EndpointRadialMargin ε W := by
  apply nonneg_of_tendsto_of_frequently_nonneg
    (tendsto_cfzp016WholeShiftedRadialMargin hε W)
  exact hdom

/-- The preceding endpoint-margin conclusion can be read directly as the
endpoint arithmetic-defect sign. -/
theorem cfzp016EndpointDefect_nonpos_of_cofinalCutoffRadialDominationAt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp016CofinalCutoffRadialDominationAt ε W) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0 := by
  exact (cfzp016EndpointRadialMargin_nonneg_iff_defectEndpoint_nonpos ε W).mp
    (cfzp016EndpointRadialMargin_nonneg_of_cofinalCutoffRadialDominationAt hε W hdom)

/-! ## Gate D: doubly cofinal radial domination -/

/-- Cofinal nonnegative radial margins are available at cofinally many
positive smoothing parameters. -/
def Cfzp016DoublyCofinalRadialDomination
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ Cfzp016CofinalCutoffRadialDominationAt ε W

/-- Doubly cofinal radial domination forces a nonnegative fixed margin. -/
theorem cfzp016FixedRadialMargin_nonneg_of_doublyCofinalRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp016DoublyCofinalRadialDomination W) :
    0 ≤ cfzp016FixedRadialMargin W := by
  apply nonneg_of_tendsto_of_frequently_nonneg
    (tendsto_cfzp016EndpointRadialMargin_epsilon W)
  exact hdom.mono fun ε hε =>
    cfzp016EndpointRadialMargin_nonneg_of_cofinalCutoffRadialDominationAt
      hε.1 W hε.2

/-- Doubly cofinal radial domination forces the fixed arithmetic defect to be
nonpositive. -/
theorem cfzp016FixedDefect_nonpos_of_doublyCofinalRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp016DoublyCofinalRadialDomination W) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  exact (cfzp016FixedRadialMargin_nonneg_iff_fixedDefect_nonpos W).mp
    (cfzp016FixedRadialMargin_nonneg_of_doublyCofinalRadialDomination W hdom)

/-! ## Gate E: finite-window criticality -/

/-- Combining double cofinality with safe-radius nonnegativity gives fixed
defect vanishing on the current finite window. -/
theorem cfzp016FixedDefect_eq_zero_of_doublyCofinalRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp016DoublyCofinalRadialDomination W) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  apply le_antisymm
  · exact cfzp016FixedDefect_nonpos_of_doublyCofinalRadialDomination W hdom
  · exact pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg W.circle_safe

/-- The double-cofinal provider forces every zero in this finite safe window
onto the critical line. -/
theorem cfzp016FiniteWindowZeros_critical_of_doublyCofinalRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp016DoublyCofinalRadialDomination W) :
    ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      ρ.re = (1 : ℝ) / 2 := by
  apply (pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
    W.circle_safe).mp
  exact cfzp016FixedDefect_eq_zero_of_doublyCofinalRadialDomination W hdom

/-! ## Gate F: weakening the CFZP-015 provider -/

/-- The stronger CFZP-015 eventual provider implies the doubly cofinal
provider, but neither provider is constructed here. -/
theorem cfzp016DoublyCofinalRadialDomination_of_cfzp015
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp015OrderedFiniteRadialDomination W) :
    Cfzp016DoublyCofinalRadialDomination W := by
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ Cfzp016CofinalCutoffRadialDominationAt ε W := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine ⟨hε, ?_⟩
    exact (hdom ε hε).frequently
  exact hev.frequently

/-! ## Gate G: the sharpened provider frontier -/

/-- The independent doubly cofinal radial-domination provider remains open. -/
inductive Cfzp016CofinalArithmeticRadialDominationGap : Prop
  | noIndependentDoublyCofinalRadialDominationProvider

end DkMath.RH.CFBRCProjection
