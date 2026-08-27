/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideNormalizedRayPolarizationOrderingAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaAmplitudeGapRayMinusObservableShapeAudit"

/-!
# CFZP-010: amplitude Gap / ray-minus observable-shape audit

This module compares the two finite quadratic shapes without identifying them.
The amplitude-side Gap is a diagonal, modewise ledger.  The source-side
ray-minus observable first forms a finite complex ray and then applies
`Complex.normSq (Z - 1)`, so its exact expansion contains a baseline and Gram
interference terms.  The missing bridge is recorded explicitly rather than
being replaced by an unsupported equality.

All results here are finite algebraic statements.  No branch-sensitive phase,
infinite cutoff exchange, provider, or RH consequence is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators ComplexConjugate Interval Topology

/-! ## Gate A: amplitude-side diagonal Gap surface -/

/-- The amplitude-side mirror-minus ledger is exactly the finite Gap ledger. -/
theorem cfzp010AggregateMirrorMinusWholeUpTo_eq_gap
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorMinusWholeUpTo X δ =
      cfzpAggregateMirrorGapUpTo X δ :=
  cfzpAggregateMirrorMinusWholeUpTo_eq_gap X δ

/-! The carrier-weighted amplitude ledger is a sum of modewise squares. -/

/-- The carrier-weighted Gap is the diagonal sum of mirror-mode differences. -/
theorem cfzp010AggregateCarrierWeightedMirrorGapUpTo_eq_modeDifferenceNormSqSum
    (X : ℕ) (s : ℂ) :
    cfzpAggregateCarrierWeightedMirrorGapUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        canonicalPrimePowerShadowCost q *
          Complex.normSq (cfzpSameHeightMirrorModeDifference q s) :=
  cfzpAggregateCarrierWeightedMirrorGapUpTo_eq_modeDifferenceNormSqSum X s

/-! The center-zero vanishing is retained as a finite adapter where available. -/

/-- The finite amplitude Gap vanishes exactly at the centered mirror height. -/
theorem cfzp010AggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ = 0 ↔ δ = 0 :=
  cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero hX δ

/-! ## Gate B: normalized source ray-minus shape -/

/-- Pointwise, the source ray-minus density is the square of `Z - 1`. -/
theorem cfzp010RayMinusDensity_eq_normSq_sub_one
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t =
      Complex.normSq
        (pascalCenteredXiPrimeSideCS25RayState ε W X p t - 1) :=
  pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_eq_cs25State_normSq_sub_one
    W hp t

/-- The normalized source shape exposes its baseline and signed interaction. -/
theorem cfzp010NormSq_sub_one_eq_normSq_add_one_sub_two_re (z : ℂ) :
    Complex.normSq (z - 1) = Complex.normSq z + 1 - 2 * z.re := by
  rw [Complex.normSq_sub]
  simp

/-- The common carrier minus interaction is the same normalized square. -/
theorem cfzp010CommonDensity_sub_interactionDensity_eq_normSq_sub_one
    (z : ℂ) :
    pascalCenteredXiPrimeSideCommonDensity z -
        pascalCenteredXiPrimeSideInteractionDensity z =
      Complex.normSq (z - 1) :=
  pascalCenteredXiPrimeSideCommonDensity_sub_interactionDensity_eq_normSq_sub_one z

/-- The aggregate ray-minus energy retains the common carrier and interaction. -/
theorem cfzp010AggregateRayMinusEnergy_eq_common_sub_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X =
      pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X -
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X :=
  pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction hε W X

/-! ## Gate C: finite ray sum before quadraticization -/

/-- The prime-power ray is definitionally a finite sum of complex summands. -/
theorem cfzp010FinitePrimePowerRayAmplitude_eq_finite_mode_sum
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
        pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t :=
  rfl

/-- The same finite ray has the existing weighted geometric-core compression. -/
theorem cfzp010FinitePrimePowerRayAmplitude_eq_weight_mul_geometricCore
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        pascalCenteredXiPrimeSideFiniteGeometricRayCore
          (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)
          (pascalCenteredXiPrimeSidePrimePowerRayLength X p) :=
  pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_weight_mul_canonicalGeometricCore
    W hp t

/-- The finite ray also has the endpoint-over-denominator compression. -/
theorem cfzp010FinitePrimePowerRayAmplitude_eq_endpoint_div
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t /
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t :=
  pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div W hp t

/-! ## Gate D: finite Gram/interference decomposition -/

/--
For a finite complex family, quadraticizing the sum produces the full
ordered Gram ledger, including off-diagonal interference terms.
-/
theorem cfzp010_normSq_sum_eq_sum_sum_re_conj_mul
    {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    Complex.normSq (∑ i ∈ S, a i) =
      ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ (a i) * a j).re := by
  classical
  have hprod :
      starRingEnd ℂ (∑ i ∈ S, a i) * (∑ j ∈ S, a j) =
        ∑ i ∈ S, ∑ j ∈ S, starRingEnd ℂ (a i) * a j := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hre := congrArg Complex.re hprod
  simpa [Complex.normSq_apply] using hre

/-- Two equal modes already show that a diagonal sum cannot replace a Gram sum. -/
theorem cfzp010_normSq_sum_not_eq_sum_normSq :
    Complex.normSq ((1 : ℂ) + 1) ≠
      Complex.normSq (1 : ℂ) + Complex.normSq (1 : ℂ) := by
  norm_num [Complex.normSq_apply]

/-! ## Gate E: the remaining bridge is a three-layer transport problem -/

/--
The old amplitude-to-ray backlog is not a one-step equality.  A provider for
this marker would have to supply all three missing layers: (1) a transform
from mirror amplitude modes to source geometric modes, (2) transport of the
Gram/interference ledger, and (3) the source baseline `1` and interaction
normalization.
-/
inductive Cfzp010AmplitudeGapToRayMinusSameObservableBridgeGap : Prop
  | noExactModeTransformInterferenceNormalizationBridgeProvided

end DkMath.RH.CFBRCProjection
