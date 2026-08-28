/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteGeometricRayAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalReflectionPrimeRayCanonicalAggregateTransportAudit"

/-!
# CFZP-014: functional-reflection prime-ray canonical aggregate transport

This module aggregates the finite functional-reflection ray over the existing
Pascal prime support and folds it through the canonical prime-power support.
The result is a finite identity with the existing symmetric Euler rate.  The
reversed right-edge observable is kept distinct from the top-edge CS38
observable; no contour relocation, limit exchange, baseline collapse, or RH
conclusion is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open scoped BigOperators ComplexConjugate Interval Topology

/-! ## Gate A: prime-weighted functional-reflection ray -/

/-- The finite prime-weighted functional-reflection ray aggregate. -/
noncomputable def cfzp014AggregateFunctionalReflectionPrimeRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    (Real.log (p : ℝ) : ℂ) *
      cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t

/-! ## Gate B/C: finite pair and canonical reindex -/

/-- The nested prime-ray sum is the existing finite pair-support sum. -/
theorem cfzp014AggregateFunctionalReflectionPrimeRayAmplitude_eq_pairSupport
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) :
    cfzp014AggregateFunctionalReflectionPrimeRayAmplitude ε W X t =
      ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        (Real.log (pk.1 : ℝ) : ℂ) *
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W t) *
          cfzpFunctionalReflectionModeDifference
            (primePowerPairLabel pk)
            (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) := by
  classical
  let s : ℂ := pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)
  let w : ℂ := pascalCenteredXiMellinSecondDifferenceWeight ε 0
    (pascalCenteredXiPrimeSideModePhaseNode W t)
  unfold cfzp014AggregateFunctionalReflectionPrimeRayAmplitude
  simp only [cfzp012FunctionalReflectionPrimePowerRayAmplitude]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  simp only [pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo,
    Finset.sum_filter]
  unfold pascalPrimePowerPairSupportUpTo
  rw [Finset.sum_filter]
  rw [← Finset.sum_product']
  simp only [primePowerPairLabel]
  rfl

/-- The aggregate folds to the canonical functional-reflection source. -/
theorem cfzp014AggregateFunctionalReflectionPrimeRayAmplitude_eq_canonical
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) :
    cfzp014AggregateFunctionalReflectionPrimeRayAmplitude ε W X t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
          (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) := by
  classical
  let s : ℂ := pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)
  let w : ℂ := pascalCenteredXiMellinSecondDifferenceWeight ε 0
    (pascalCenteredXiPrimeSideModePhaseNode W t)
  have hpair := cfzp014AggregateFunctionalReflectionPrimeRayAmplitude_eq_pairSupport
    ε W X t
  rw [hpair]
  unfold cfzpCanonicalFunctionalReflectionLinearSourceUpTo
  rw [← image_primePowerPairLabel_support_eq_canonicalSupport]
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun pk _ => primePowerPairLabel pk)
  · intro pk hpk
    exact Finset.mem_image.mpr ⟨pk, hpk, rfl⟩
  · intro a ha b hb hab
    exact primePowerPairLabel_injOn X ha hb hab
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨pk, hpk, rfl⟩
    exact ⟨pk, hpk, rfl⟩
  · intro pk hpk
    have hsupport := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
    have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsupport.1).1
    rw [canonicalPrimePowerShadowCost_eq_log_of_witness hp (by omega)
      (q := primePowerPairLabel pk) (p := pk.1) (j := pk.2 + 1) rfl]
    simp only [primePowerPairLabel]
    ring

/-! ## Gate D: finite symmetric Euler rate -/

/-- The canonical aggregate is the reversed-right-edge symmetric Euler rate. -/
theorem cfzp014AggregateFunctionalReflectionPrimeRayAmplitude_eq_finiteSymmetricEulerRate
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) :
    cfzp014AggregateFunctionalReflectionPrimeRayAmplitude ε W X t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
          (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) := by
  rw [cfzp014AggregateFunctionalReflectionPrimeRayAmplitude_eq_canonical]
  rw [cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate]

/-! ## Gate F: the edge relocation frontier -/

/-- Right-edge functional reflection has no supplied top-edge relocation. -/
inductive Cfzp014FunctionalReflectionRightToTopEdgeTransportGap : Prop
  | noExactRightEdgeToTopEdgeFunctionalReflectionTransportProvided

end DkMath.RH.CFBRCProjection
