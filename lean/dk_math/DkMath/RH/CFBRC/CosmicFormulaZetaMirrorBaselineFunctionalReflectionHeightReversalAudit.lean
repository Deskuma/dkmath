/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSameHeightMirrorSourceModeTransformAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaMirrorBaselineFunctionalReflectionHeightReversalAudit"

/-!
# CFZP-012: mirror-baseline functional-reflection height reversal audit

This module compares the same-height mirror source with the existing
functional-reflection source after reversing the finite right-edge height.
The comparison is finite and algebraic.  It isolates the vertical
displacement term and the possible Mellin-weight reversal correction without
identifying the mirror baseline residual with a common-energy defect.

No phase branch, infinite cutoff, limit exchange, positivity provider, or RH
consequence is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators ComplexConjugate Interval Topology

/-! ## Gate A: coordinate height reversal -/

/-- Critical reflection of the right-edge point is functional reflection at `-t`. -/
theorem cfzp012CriticalMirror_rightEdge_eq_one_sub_rightEdge_neg
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    criticalMirror (pascalSymmetricRectangleRightEdge W.rectangle.σ t) =
      1 - pascalSymmetricRectangleRightEdge W.rectangle.σ (-t) := by
  apply Complex.ext <;>
    simp [criticalMirror, pascalSymmetricRectangleRightEdge]

/-- The centered right-edge mode node reverses by complex conjugation. -/
theorem cfzp012ModePhaseNode_neg_eq_conj
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    pascalCenteredXiPrimeSideModePhaseNode W (-t) =
      conj (pascalCenteredXiPrimeSideModePhaseNode W t) := by
  rw [pascalCenteredXiPrimeSideModePhaseNode_eq_affine,
    pascalCenteredXiPrimeSideModePhaseNode_eq_affine]
  apply Complex.ext <;> simp

/-! ## Gate B: functional reflection plus vertical displacement -/

/-- Same-height mirror mode at `t` equals reversed functional reflection plus
the vertical displacement between the two right-edge heights. -/
theorem cfzp012SameHeightMirrorModeDifference_eq_reversedFunctional_add_verticalDisplacement
    (q : ℕ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    cfzpSameHeightMirrorModeDifference q
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t) =
      cfzpFunctionalReflectionModeDifference q
        (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) +
        (((q : ℂ) ^
            (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)))) -
          (q : ℂ) ^
            (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))) := by
  have hcoord := cfzp012CriticalMirror_rightEdge_eq_one_sub_rightEdge_neg W t
  unfold cfzpSameHeightMirrorModeDifference
    cfzpFunctionalReflectionModeDifference
  rw [hcoord]
  ring

/-! ## Gate C: Mellin-weighted summand transport -/

/-- A right source mode evaluated at reversed height, with the current time's
Mellin weight retained. -/
noncomputable def cfzp012ReweightedReversedRightSourceSummand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    (((p ^ (k + 1) : ℕ) : ℂ) ^
      (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))))

/-- The same-height mirror summand minus the reweighted reversed-right
summand is the weighted functional-reflection mode. -/
theorem cfzp012MirrorSourceSummand_sub_reweightedReversedRight_eq_weight_mul_functionalReflectionModeDifference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) :
    cfzp011SameHeightMirrorSourceSummand ε W p k t -
        cfzp012ReweightedReversedRightSourceSummand ε W p k t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        cfzpFunctionalReflectionModeDifference
          (p ^ (k + 1))
          (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) := by
  have hcoord := cfzp012CriticalMirror_rightEdge_eq_one_sub_rightEdge_neg W t
  unfold cfzp011SameHeightMirrorSourceSummand
    cfzp012ReweightedReversedRightSourceSummand
    cfzpFunctionalReflectionModeDifference
  rw [hcoord]
  ring

/-- The same-height mirror/right difference splits into functional-reflection
and vertical-displacement contributions with the same current-time weight. -/
theorem cfzp012MirrorSourceSummand_sub_rightSourceSummand_eq_functional_add_vertical
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) :
    cfzp011SameHeightMirrorSourceSummand ε W p k t -
        pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        (cfzpFunctionalReflectionModeDifference
          (p ^ (k + 1))
          (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) +
          (((p ^ (k + 1) : ℕ) : ℂ) ^
              (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))) -
            ((p ^ (k + 1) : ℕ) : ℂ) ^
              (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) := by
  have hcoord := cfzp012CriticalMirror_rightEdge_eq_one_sub_rightEdge_neg W t
  unfold cfzp011SameHeightMirrorSourceSummand
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
    cfzpFunctionalReflectionModeDifference
  rw [hcoord]
  ring

/-! ## Gate D: finite ray transport -/

/-- The finite reweighted reversed-right ray over the existing support. -/
noncomputable def cfzp012ReweightedReversedRightPrimePowerRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
    cfzp012ReweightedReversedRightSourceSummand ε W p k t

/-- The finite functional-reflection contribution carried by the same support. -/
noncomputable def cfzp012FunctionalReflectionPrimePowerRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalCenteredXiPrimeSideModePhaseNode W t) *
      cfzpFunctionalReflectionModeDifference
        (p ^ (k + 1))
        (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))

/-- The finite mirror ray is functional-reflection contribution plus the
reweighted reversed-right ray. -/
theorem cfzp012SameHeightMirrorRay_eq_functionalReflection_add_reweightedReversedRight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t =
      cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
        cfzp012ReweightedReversedRightPrimePowerRayAmplitude ε W X p t := by
  unfold cfzp011SameHeightMirrorPrimePowerRayAmplitude
    cfzp012FunctionalReflectionPrimePowerRayAmplitude
    cfzp012ReweightedReversedRightPrimePowerRayAmplitude
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hcoord := cfzp012CriticalMirror_rightEdge_eq_one_sub_rightEdge_neg W t
  unfold cfzp011SameHeightMirrorSourceSummand
    cfzp012ReweightedReversedRightSourceSummand
    cfzpFunctionalReflectionModeDifference
  rw [hcoord]
  ring

/-- The mirror baseline residual is localized to functional reflection and a
reweighted reversed-right residual. -/
theorem cfzp012SameHeightMirrorRay_sub_one_eq_functionalReflection_add_reversedRightResidual
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t - 1 =
      cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t +
        (cfzp012ReweightedReversedRightPrimePowerRayAmplitude ε W X p t - 1) := by
  rw [cfzp012SameHeightMirrorRay_eq_functionalReflection_add_reweightedReversedRight]
  ring

/-! ## Gate E/F: explicit weight-reversal correction -/

/-- The reweighted reversed-right summand differs from the actual right
summand at `-t` only by the Mellin-weight mismatch. -/
theorem cfzp012ReweightedReversedRightSourceSummand_sub_actualRightAtNeg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) :
    cfzp012ReweightedReversedRightSourceSummand ε W p k t -
        pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k (-t) =
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) -
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W (-t))) *
        (((p ^ (k + 1) : ℕ) : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))) : ℂ) := by
  unfold cfzp012ReweightedReversedRightSourceSummand
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
  ring

/-- The finite reweighted-ray correction against the actual right ray at
`-t` is an explicit finite sum of weight mismatches. -/
theorem cfzp012ReweightedReversedRightRay_sub_actualRightRayAtNeg_eq_weightCorrection
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    cfzp012ReweightedReversedRightPrimePowerRayAmplitude ε W X p t -
        pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t) =
      ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W t) -
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W (-t))) *
          (((p ^ (k + 1) : ℕ) : ℂ) ^
            (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))) : ℂ) := by
  unfold cfzp012ReweightedReversedRightPrimePowerRayAmplitude
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact cfzp012ReweightedReversedRightSourceSummand_sub_actualRightAtNeg ε W p k t

/-! ## Explicit frontier -/

/-- The remaining Gate E correction is the unproved weight-reversal/conjugation
provider; no symmetry of the Mellin weight is silently assumed. -/
inductive Cfzp012WeightReversalConjugationGap : Prop
  | noWeightReversalConjugationProvider

end DkMath.RH.CFBRCProjection
