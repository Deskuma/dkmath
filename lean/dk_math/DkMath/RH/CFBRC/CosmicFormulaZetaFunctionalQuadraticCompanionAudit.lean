/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalQuadraticCompanionAudit"

/-!
# CFZP-006C: functional quadratic companion audit

This module quadraticizes the CFZP functional-reflection source while keeping
all interference terms explicit.  The mode identity is the sum of cycle,
same-height, and signed cross terms.  The finite diagonal ledger uses the
original linear source weight, while the squared norm of the total linear
source has a squared-weight diagonal and a separate cross-mode remainder.

The same-height diagonal is exactly the CFZP-004 carrier-weighted mirror Gap
ledger.  No `normSq`-of-a-sum distribution, CompletionRemainder bridge,
Mellin Gram bridge, phase branch, or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Mode-level quadratic companion -/

noncomputable def cfzpFunctionalReflectionModeQuadraticMass
    (q : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (cfzpFunctionalReflectionModeDifference q s)

noncomputable def cfzpCycleDisplacementModeQuadraticMass
    (q : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (cfzpFunctionalVsSameHeightCycleDisplacementMode q s)

noncomputable def cfzpSameHeightMirrorModeQuadraticMass
    (q : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (cfzpSameHeightMirrorModeDifference q s)

noncomputable def cfzpCycleSameHeightModeCrossTerm
    (q : ℕ) (s : ℂ) : ℝ :=
  2 * (cfzpFunctionalVsSameHeightCycleDisplacementMode q s *
    conj (cfzpSameHeightMirrorModeDifference q s)).re

theorem cfzpFunctionalReflectionModeQuadraticMass_eq_cycle_add_sameHeight_add_cross
    (q : ℕ) (s : ℂ) :
    cfzpFunctionalReflectionModeQuadraticMass q s =
      cfzpCycleDisplacementModeQuadraticMass q s +
        cfzpSameHeightMirrorModeQuadraticMass q s +
          cfzpCycleSameHeightModeCrossTerm q s := by
  unfold cfzpFunctionalReflectionModeQuadraticMass
    cfzpCycleDisplacementModeQuadraticMass
    cfzpSameHeightMirrorModeQuadraticMass
    cfzpCycleSameHeightModeCrossTerm
  rw [cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight]
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

theorem cfzpSameHeightMirrorModeQuadraticMass_eq_carrier_mul_gap
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpSameHeightMirrorModeQuadraticMass q s =
      Complex.normSq (cfzpPrimePowerSameHeightCommonCarrier q s) *
        primeMirrorOffsetGap q (centeredSigma s.re) := by
  unfold cfzpSameHeightMirrorModeQuadraticMass
  exact normSq_cfzpSameHeightMirrorModeDifference hq s

theorem cfzpFunctionalReflectionModeQuadraticMass_eq_sameHeight_of_im_eq_zero
    {q : ℕ} {s : ℂ} (hs : s.im = 0) :
    cfzpFunctionalReflectionModeQuadraticMass q s =
      cfzpSameHeightMirrorModeQuadraticMass q s := by
  unfold cfzpFunctionalReflectionModeQuadraticMass
    cfzpSameHeightMirrorModeQuadraticMass
  rw [cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight,
    cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_zero_of_im_eq_zero hs]
  simp

theorem cfzpFunctionalReflectionModeQuadraticMass_eq_cycle_of_re_eq_half
    {q : ℕ} {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    cfzpFunctionalReflectionModeQuadraticMass q s =
      cfzpCycleDisplacementModeQuadraticMass q s := by
  unfold cfzpFunctionalReflectionModeQuadraticMass
    cfzpCycleDisplacementModeQuadraticMass
  rw [cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight,
    cfzpSameHeightMirrorModeDifference_eq_zero_of_re_eq_half hs]
  simp

theorem cfzpFunctionalReflectionModeQuadraticMass_eq_zero_of_re_eq_half_of_im_eq_zero
    {q : ℕ} {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (him : s.im = 0) :
    cfzpFunctionalReflectionModeQuadraticMass q s = 0 := by
  rw [cfzpFunctionalReflectionModeQuadraticMass_eq_cycle_of_re_eq_half hre]
  unfold cfzpCycleDisplacementModeQuadraticMass
  rw [cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_zero_of_im_eq_zero him]
  simp

theorem cfzpFunctionalReflectionModeQuadraticMass_nonneg
    (q : ℕ) (s : ℂ) :
    0 ≤ cfzpFunctionalReflectionModeQuadraticMass q s := by
  unfold cfzpFunctionalReflectionModeQuadraticMass
  exact Complex.normSq_nonneg _

theorem cfzpCycleDisplacementModeQuadraticMass_nonneg
    (q : ℕ) (s : ℂ) :
    0 ≤ cfzpCycleDisplacementModeQuadraticMass q s := by
  unfold cfzpCycleDisplacementModeQuadraticMass
  exact Complex.normSq_nonneg _

theorem cfzpSameHeightMirrorModeQuadraticMass_nonneg
    (q : ℕ) (s : ℂ) :
    0 ≤ cfzpSameHeightMirrorModeQuadraticMass q s := by
  unfold cfzpSameHeightMirrorModeQuadraticMass
  exact Complex.normSq_nonneg _

/-! ## B. Linear-weight finite diagonal ledger -/

noncomputable def cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cfzpFunctionalReflectionModeQuadraticMass q s

noncomputable def cfzpAggregateCycleDisplacementQuadraticLedgerUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cfzpCycleDisplacementModeQuadraticMass q s

noncomputable def cfzpAggregateCycleSameHeightCrossLedgerUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cfzpCycleSameHeightModeCrossTerm q s

theorem cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo_eq_cycle_add_gap_add_cross
    (X : ℕ) (s : ℂ) :
    cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo X s =
      cfzpAggregateCycleDisplacementQuadraticLedgerUpTo X s +
        cfzpAggregateCarrierWeightedMirrorGapUpTo X s +
          cfzpAggregateCycleSameHeightCrossLedgerUpTo X s := by
  rw [cfzpAggregateCarrierWeightedMirrorGapUpTo_eq_modeDifferenceNormSqSum]
  unfold cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo
    cfzpAggregateCycleDisplacementQuadraticLedgerUpTo
    cfzpAggregateCycleSameHeightCrossLedgerUpTo
  calc
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
        canonicalPrimePowerShadowCost q *
          cfzpFunctionalReflectionModeQuadraticMass q s) =
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            (cfzpCycleDisplacementModeQuadraticMass q s +
              cfzpSameHeightMirrorModeQuadraticMass q s +
              cfzpCycleSameHeightModeCrossTerm q s) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [cfzpFunctionalReflectionModeQuadraticMass_eq_cycle_add_sameHeight_add_cross]
    _ = (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            cfzpCycleDisplacementModeQuadraticMass q s) +
        (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            Complex.normSq (cfzpSameHeightMirrorModeDifference q s)) +
        (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            cfzpCycleSameHeightModeCrossTerm q s) := by
      simp_rw [cfzpSameHeightMirrorModeQuadraticMass, mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo_eq_gap_of_im_eq_zero
    {X : ℕ} {s : ℂ} (hs : s.im = 0) :
    cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo X s =
      cfzpAggregateCarrierWeightedMirrorGapUpTo X s := by
  rw [cfzpAggregateCarrierWeightedMirrorGapUpTo_eq_modeDifferenceNormSqSum]
  unfold cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo
  apply Finset.sum_congr rfl
  intro q hq
  rw [cfzpFunctionalReflectionModeQuadraticMass_eq_sameHeight_of_im_eq_zero hs]
  rfl

theorem cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo_eq_cycle_of_re_eq_half
    {X : ℕ} {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo X s =
      cfzpAggregateCycleDisplacementQuadraticLedgerUpTo X s := by
  unfold cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo
    cfzpAggregateCycleDisplacementQuadraticLedgerUpTo
  apply Finset.sum_congr rfl
  intro q hq
  rw [cfzpFunctionalReflectionModeQuadraticMass_eq_cycle_of_re_eq_half hs]

theorem cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo_eq_zero_of_re_eq_half_of_im_eq_zero
    {X : ℕ} {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (him : s.im = 0) :
    cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo X s = 0 := by
  unfold cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo
  apply Finset.sum_eq_zero
  intro q hq
  rw [cfzpFunctionalReflectionModeQuadraticMass_eq_zero_of_re_eq_half_of_im_eq_zero
    hre him]
  ring

theorem cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo X s := by
  unfold cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg
    (canonicalPrimePowerShadowCost_pos_of_mem hq).le
    (cfzpFunctionalReflectionModeQuadraticMass_nonneg q s)

theorem cfzpAggregateCycleDisplacementQuadraticLedgerUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpAggregateCycleDisplacementQuadraticLedgerUpTo X s := by
  unfold cfzpAggregateCycleDisplacementQuadraticLedgerUpTo
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg
    (canonicalPrimePowerShadowCost_pos_of_mem hq).le
    (cfzpCycleDisplacementModeQuadraticMass_nonneg q s)

/-! ## C. Total source mass and cross-mode interference -/

noncomputable def cfzpCanonicalFunctionalReflectionScaledMode
    (q : ℕ) (s : ℂ) : ℂ :=
  (canonicalPrimePowerShadowCost q : ℂ) *
    cfzpFunctionalReflectionModeDifference q s

theorem normSq_cfzpCanonicalFunctionalReflectionScaledMode
    (q : ℕ) (s : ℂ) :
    Complex.normSq (cfzpCanonicalFunctionalReflectionScaledMode q s) =
      (canonicalPrimePowerShadowCost q) ^ 2 *
        cfzpFunctionalReflectionModeQuadraticMass q s := by
  unfold cfzpCanonicalFunctionalReflectionScaledMode
    cfzpFunctionalReflectionModeQuadraticMass
  rw [Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  ring

noncomputable def cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q) ^ 2 *
      cfzpFunctionalReflectionModeQuadraticMass q s

theorem cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo_eq_scaledModeNormSqSum
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        Complex.normSq (cfzpCanonicalFunctionalReflectionScaledMode q s) := by
  unfold cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo
  apply Finset.sum_congr rfl
  intro q hq
  exact (normSq_cfzpCanonicalFunctionalReflectionScaledMode q s).symm

theorem cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s := by
  rw [cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo_eq_scaledModeNormSqSum]
  apply Finset.sum_nonneg
  intro q hq
  exact Complex.normSq_nonneg _

noncomputable def cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s)

theorem cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo
  exact Complex.normSq_nonneg _

noncomputable def cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s -
    cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s

theorem cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo_eq_diagonal_add_crossMode
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s =
      cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s +
        cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo
  ring

/-! The cross-mode term is kept difference-defined; no off-diagonal pair sum
    or Mellin Gram identification is asserted in this checkpoint. -/

inductive CfzpLinearWeightToSquaredWeightBridgeGap : Prop
  | noExactWeightDegreeIdentificationProvided

inductive CfzpCompletionRemainderQuadraticCompanionBridgeGap : Prop
  | noExactRemainderQuadraticIdentificationProvided

end DkMath.RH.CFBRCProjection
