/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaAmplitudeGapRayMinusObservableShapeAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteGeometricRayAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSameHeightMirrorSourceModeTransformAudit"

/-!
# CFZP-011: same-height mirror/source mode-transform audit

This module closes only the finite mode transform from a same-height mirror
amplitude mode to its Mellin-weighted source mode.  The Mellin norm factor is
kept explicit.  The finite Gram transport and the mirror baseline residual
remain separate from this layer.

No source/ray equality with the amplitude Gap, infinite cutoff exchange,
branch-sensitive phase statement, or RH consequence is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators ComplexConjugate Interval Topology

/-! ## Gate A: the right source mode -/

/-- The existing source summand is the Mellin weight times the right mode. -/
theorem cfzp011RightSourceSummand_eq_weight_mul_mode
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        (((p ^ (k + 1) : ℕ) : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))) :=
  rfl

/-! ## Gate B: same-height mirror source mode -/

/-- The same-height mirror mate of one finite source summand. -/
noncomputable def cfzp011SameHeightMirrorSourceSummand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    (((p ^ (k + 1) : ℕ) : ℂ) ^
      (-(criticalMirror
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t))))

/-- The mirror/right source pair is the weighted same-height mode difference. -/
theorem cfzp011MirrorSourceSummand_sub_rightSourceSummand_eq_weight_mul_sameHeightModeDifference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) :
    cfzp011SameHeightMirrorSourceSummand ε W p k t -
        pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        cfzpSameHeightMirrorModeDifference
          (p ^ (k + 1))
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
  unfold cfzp011SameHeightMirrorSourceSummand
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
    cfzpSameHeightMirrorModeDifference
  ring

/-! ## Gate C: modewise quadratic transport -/

/-- Quadraticizing the source pair leaves the Mellin weight norm explicit. -/
theorem cfzp011MirrorSourcePairDifference_normSq_eq_weightNormSq_mul_amplitudeModeGap
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) :
    Complex.normSq
        (cfzp011SameHeightMirrorSourceSummand ε W p k t -
          pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t) =
      Complex.normSq
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W t)) *
        Complex.normSq
          (cfzpSameHeightMirrorModeDifference
            (p ^ (k + 1))
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
  rw [cfzp011MirrorSourceSummand_sub_rightSourceSummand_eq_weight_mul_sameHeightModeDifference,
    Complex.normSq_mul]

/-- The modewise transport can also be expanded through the existing Gap factor. -/
theorem cfzp011MirrorSourcePairDifference_normSq_eq_weight_carrier_gap
    {p k : ℕ} (hp : 0 < p)
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    Complex.normSq
        (cfzp011SameHeightMirrorSourceSummand ε W p k t -
          pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t) =
      Complex.normSq
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W t)) *
        (Complex.normSq
            (cfzpPrimePowerSameHeightCommonCarrier
              (p ^ (k + 1))
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          primeMirrorOffsetGap
            (p ^ (k + 1))
            (centeredSigma
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t).re)) := by
  rw [cfzp011MirrorSourcePairDifference_normSq_eq_weightNormSq_mul_amplitudeModeGap,
    normSq_cfzpSameHeightMirrorModeDifference]
  exact pow_pos hp (k + 1)

/-! ## Gate D: finite same-height mirror ray -/

/-- The finite same-height mirror ray over the existing exponent support. -/
noncomputable def cfzp011SameHeightMirrorPrimePowerRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
    cfzp011SameHeightMirrorSourceSummand ε W p k t

/-- The finite mirror ray minus the right ray is the weighted mode-difference sum. -/
theorem cfzp011MirrorRay_sub_rightRay_eq_sum_weighted_sameHeightModeDifference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t -
        pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W t) *
          cfzpSameHeightMirrorModeDifference
            (p ^ (k + 1))
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
  unfold cfzp011SameHeightMirrorPrimePowerRayAmplitude
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact cfzp011MirrorSourceSummand_sub_rightSourceSummand_eq_weight_mul_sameHeightModeDifference
    ε W p k t

/-! ## Gate E: the mirror baseline residual -/

/-- The right-ray baseline splits into a transformed part and mirror residual. -/
theorem cfzp011RightRay_sub_one_eq_transformedAmplitudePart_add_mirrorBaselineResidual
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t - 1 =
      (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t -
          cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t) +
        (cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t - 1) := by
  ring

/-- The ray-minus square retains both quadratic pieces and their interference. -/
theorem cfzp011RayMinusNormSq_eq_transformedAmplitude_add_mirrorResidual_add_interference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    Complex.normSq
        (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t - 1) =
      Complex.normSq
          (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t -
            cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t) +
        Complex.normSq
          (cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t - 1) +
        2 *
          ((pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t -
              cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t) *
            conj (cfzp011SameHeightMirrorPrimePowerRayAmplitude ε W X p t - 1)).re := by
  rw [cfzp011RightRay_sub_one_eq_transformedAmplitudePart_add_mirrorBaselineResidual,
    Complex.normSq_add]

/-! ## Gate F: explicit remaining frontier -/

/-- The remaining source-side bridge needs baseline collapse or Gram transport. -/
inductive Cfzp011MirrorBaselineResidualAndInterferenceBridgeGap : Prop
  | noMirrorBaselineResidualCollapseOrInterferenceProvider

end DkMath.RH.CFBRCProjection
