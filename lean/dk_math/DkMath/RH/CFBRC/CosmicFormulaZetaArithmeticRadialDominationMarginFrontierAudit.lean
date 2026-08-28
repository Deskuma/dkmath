/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalReflectionPrimeRayCanonicalAggregateTransportAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaArithmeticRadialDominationMarginFrontierAudit"

/-!
# CFZP-015: arithmetic radial-domination margin frontier

This module repackages the existing finite arithmetic defect as a radial
domination margin.  The margin identity and its ordered sign transport are
conditional: no independent eventual domination provider is constructed.
The fixed conclusion is limited to the supplied boundary-safe finite window;
no global RH theorem, joint limit, or contour relocation is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gate A: radial comparison adapter -/

/-- The finite radial comparison is exactly the arithmetic defect sign. -/
theorem cfzp015RadialComparison_iff_defect_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiMellinQuadraticScalarSurface ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0 := by
  exact pascalCenteredXiPrimeSideQuadraticization_radial_le_scalarSurface_iff_defect_nonpos
    hε W X

/-! ## Gate B: the whole shifted radial margin -/

/-- Difference of the two whole shifted energies above the fixed radial cost. -/
noncomputable def cfzp015WholeShiftedRadialMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X -
    pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X) -
  4 * Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R

/-- The whole shifted margin is `-4π` times the finite arithmetic defect. -/
theorem cfzp015WholeShiftedRadialMargin_eq_neg_four_mul_pi_mul_defect
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp015WholeShiftedRadialMargin ε W X =
      -4 * Real.pi *
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X := by
  have hsurface :=
    pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_shiftedEnergyDifference
      hε W X
  have hexcess := pascalCenteredXiMellinQuadraticScalarExcess_eq_neg_pi_mul_defect
    hε W X
  unfold cfzp015WholeShiftedRadialMargin
  calc
    _ = 4 * pascalCenteredXiMellinQuadraticScalarExcess ε W X := by
      rw [← hsurface]
      unfold pascalCenteredXiMellinQuadraticScalarExcess
      ring
    _ = 4 * (-Real.pi *
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X) := by
      rw [hexcess]
    _ = _ := by ring

/-- Nonnegative margin is equivalent to nonpositive finite defect. -/
theorem cfzp015WholeShiftedRadialMargin_nonneg_iff_defect_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0 := by
  rw [cfzp015WholeShiftedRadialMargin_eq_neg_four_mul_pi_mul_defect hε W X]
  have hpi : 0 < (4 : ℝ) * Real.pi := by positivity
  have hfactor :
      -4 * Real.pi * pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X =
        -(4 * Real.pi) * pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X := by
    ring
  rw [hfactor]
  constructor
  · intro h
    have hprod : (4 * Real.pi) *
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0 := by
      linarith
    exact nonpos_of_mul_nonpos_right hprod hpi
  · intro h
    have hprod : (4 * Real.pi) *
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpi.le h
    linarith

/-- The margin also records the shifted-energy comparison without ordering the
individual shifted energies. -/
theorem cfzp015WholeShiftedRadialMargin_nonneg_iff_shiftedEnergy_gap_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      4 * Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X -
          pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X := by
  unfold cfzp015WholeShiftedRadialMargin
  constructor <;> intro h <;> linarith

/-- The shifted-energy margin is equivalent to the scalar radial comparison. -/
theorem cfzp015WholeShiftedRadialMargin_nonneg_iff_scalar_radial_comparison
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiMellinQuadraticScalarSurface ε W X := by
  rw [cfzp015WholeShiftedRadialMargin_nonneg_iff_defect_nonpos hε W X,
    cfzp015RadialComparison_iff_defect_nonpos hε W X]

/-! ## Gate C: the ordered finite provider proposition -/

/-- Eventual nonnegativity of the finite radial-domination margin. -/
def Cfzp015OrderedFiniteRadialDomination
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ X : ℕ in atTop,
      0 ≤ cfzp015WholeShiftedRadialMargin ε W X

/-! ## Gate D: conditional ordered-limit transport -/

/-- An ordered finite radial provider forces the fixed defect to be nonpositive. -/
theorem cfzp015FixedDefect_nonpos_of_orderedFiniteRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp015OrderedFiniteRadialDomination W) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  apply pascalCenteredXiFixedDefect_nonpos_of_eventually_endpoint_nonpos W
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply pascalCenteredXiArithmeticDefectEndpoint_nonpos_of_eventually_approximant_nonpos
    hε W
  filter_upwards [hdom ε hε] with X hX
  exact (cfzp015WholeShiftedRadialMargin_nonneg_iff_defect_nonpos hε W X).mp hX

/-- Combining the provider with safe-radius nonnegativity gives fixed-defect
vanishing on the current finite window. -/
theorem cfzp015FixedDefect_eq_zero_of_orderedFiniteRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp015OrderedFiniteRadialDomination W) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  apply le_antisymm
  · exact cfzp015FixedDefect_nonpos_of_orderedFiniteRadialDomination W hdom
  · exact pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg W.circle_safe

/-- The same conditional provider forces every zero in this finite safe window
onto the critical line. -/
theorem cfzp015FiniteWindowZeros_critical_of_orderedFiniteRadialDomination
    (W : PascalCenteredXiResidueTransportWindow)
    (hdom : Cfzp015OrderedFiniteRadialDomination W) :
    ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      ρ.re = (1 : ℝ) / 2 := by
  apply (pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
    W.circle_safe).mp
  exact cfzp015FixedDefect_eq_zero_of_orderedFiniteRadialDomination W hdom

/-! ## Gate F: the unresolved provider frontier -/

/-- No independent eventual whole-shifted radial domination provider is supplied. -/
inductive Cfzp015ArithmeticRadialDominationGap : Prop
  | noIndependentEventualWholeShiftedRadialDominationProvider

end DkMath.RH.CFBRCProjection
