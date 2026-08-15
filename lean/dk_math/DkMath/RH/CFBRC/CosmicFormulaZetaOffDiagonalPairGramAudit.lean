/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalQuadraticCompanionAudit
import DkMath.Analysis.MellinQuadraticGramKernel
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaOffDiagonalPairGramAudit"

/-!
# CFZP-006D: off-diagonal pair and Gram-index audit

The finite quadratic mass of the canonical functional-reflection source is
expanded on the prime-power labels of the source.  This module keeps the
ordered pair convention explicit: the diagonal is separated with `erase`,
and the remaining ordered pairs are the cross-mode interference term.

The Mellin quadratic Gram API is imported only as a comparison boundary.  Its
indices are spectral nodes, whereas the pair kernel below is indexed by
prime-power labels; no source-derived identification between these indices is
asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. The prime-power pair kernel -/

noncomputable def cfzpCanonicalFunctionalReflectionPairReal
    (q r : ℕ) (s : ℂ) : ℝ :=
  (cfzpCanonicalFunctionalReflectionScaledMode q s *
    conj (cfzpCanonicalFunctionalReflectionScaledMode r s)).re

theorem cfzpCanonicalFunctionalReflectionPairReal_comm
    (q r : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionPairReal q r s =
      cfzpCanonicalFunctionalReflectionPairReal r q s := by
  unfold cfzpCanonicalFunctionalReflectionPairReal
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem cfzpCanonicalFunctionalReflectionPairReal_diag
    (q : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionPairReal q q s =
      Complex.normSq (cfzpCanonicalFunctionalReflectionScaledMode q s) := by
  unfold cfzpCanonicalFunctionalReflectionPairReal
  rw [Complex.mul_conj]
  rfl

theorem cfzpCanonicalFunctionalReflectionPairReal_eq_squaredWeight_mul_modeMass
    (q : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionPairReal q q s =
      (canonicalPrimePowerShadowCost q) ^ 2 *
        cfzpFunctionalReflectionModeQuadraticMass q s := by
  rw [cfzpCanonicalFunctionalReflectionPairReal_diag]
  exact normSq_cfzpCanonicalFunctionalReflectionScaledMode q s

theorem cfzpCanonicalFunctionalReflectionPairReal_eq_weight_mul_weight_mul_re
    (q r : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionPairReal q r s =
      canonicalPrimePowerShadowCost q *
        canonicalPrimePowerShadowCost r *
          (cfzpFunctionalReflectionModeDifference q s *
            conj (cfzpFunctionalReflectionModeDifference r s)).re := by
  unfold cfzpCanonicalFunctionalReflectionPairReal
    cfzpCanonicalFunctionalReflectionScaledMode
  simp only [map_mul, Complex.conj_ofReal]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-! ## B. Full, diagonal, and off-diagonal finite pair sums -/

noncomputable def cfzpCanonicalFunctionalReflectionFullPairSumUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    ∑ r ∈ canonicalPrimePowerSupportUpTo X,
      cfzpCanonicalFunctionalReflectionPairReal q r s

noncomputable def cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    cfzpCanonicalFunctionalReflectionPairReal q q s

noncomputable def cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    ∑ r ∈ (canonicalPrimePowerSupportUpTo X).erase q,
      cfzpCanonicalFunctionalReflectionPairReal q r s

private theorem cfzp_scaledMode_double_sum_eq_sum_mul_conj_sum
    (X : ℕ) (s : ℂ) :
    ∑ q ∈ canonicalPrimePowerSupportUpTo X,
      ∑ r ∈ canonicalPrimePowerSupportUpTo X,
        cfzpCanonicalFunctionalReflectionScaledMode q s *
          conj (cfzpCanonicalFunctionalReflectionScaledMode r s) =
      (∑ q ∈ canonicalPrimePowerSupportUpTo X,
        cfzpCanonicalFunctionalReflectionScaledMode q s) *
        conj (∑ r ∈ canonicalPrimePowerSupportUpTo X,
          cfzpCanonicalFunctionalReflectionScaledMode r s) := by
  rw [map_sum]
  exact (Finset.sum_mul_sum _ _ _ _).symm

theorem cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_totalSourceMass
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionFullPairSumUpTo X s =
      cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionFullPairSumUpTo
    cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo
  change
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
      ∑ r ∈ canonicalPrimePowerSupportUpTo X,
        (cfzpCanonicalFunctionalReflectionScaledMode q s *
          conj (cfzpCanonicalFunctionalReflectionScaledMode r s)).re) =
      Complex.normSq
        (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          cfzpCanonicalFunctionalReflectionScaledMode q s)
  calc
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
        ∑ r ∈ canonicalPrimePowerSupportUpTo X,
          (cfzpCanonicalFunctionalReflectionScaledMode q s *
            conj (cfzpCanonicalFunctionalReflectionScaledMode r s)).re) =
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          (∑ r ∈ canonicalPrimePowerSupportUpTo X,
            cfzpCanonicalFunctionalReflectionScaledMode q s *
              conj (cfzpCanonicalFunctionalReflectionScaledMode r s)).re := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Complex.re_sum]
    _ = (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          ∑ r ∈ canonicalPrimePowerSupportUpTo X,
            cfzpCanonicalFunctionalReflectionScaledMode q s *
              conj (cfzpCanonicalFunctionalReflectionScaledMode r s)).re := by
      rw [Complex.re_sum]
    _ = ((∑ q ∈ canonicalPrimePowerSupportUpTo X,
          cfzpCanonicalFunctionalReflectionScaledMode q s) *
        conj (∑ r ∈ canonicalPrimePowerSupportUpTo X,
          cfzpCanonicalFunctionalReflectionScaledMode r s)).re := by
      rw [cfzp_scaledMode_double_sum_eq_sum_mul_conj_sum]
    _ = Complex.normSq
        (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          cfzpCanonicalFunctionalReflectionScaledMode q s) := by
      rw [Complex.mul_conj]
      rfl

theorem cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo_eq_squaredWeightDiagonal
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo X s =
      cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo
    cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo
  apply Finset.sum_congr rfl
  intro q hq
  exact cfzpCanonicalFunctionalReflectionPairReal_eq_squaredWeight_mul_modeMass q s

theorem cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_diagonal_add_offDiagonal
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionFullPairSumUpTo X s =
      cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo X s +
        cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionFullPairSumUpTo
    cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo
    cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [add_comm, ← Finset.sum_erase_add _ _ hq]

theorem cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo_eq_offDiagonalPairSum
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo X s =
      cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo X s := by
  calc
    cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo X s =
        cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s -
          cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s := rfl
    _ = cfzpCanonicalFunctionalReflectionFullPairSumUpTo X s -
          cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo X s := by
      rw [cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_totalSourceMass,
        cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo_eq_squaredWeightDiagonal]
    _ = cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo X s := by
      rw [cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_diagonal_add_offDiagonal]
      ring

/-! ## C. Positivity and the index/Gram boundary -/

theorem cfzpCanonicalFunctionalReflectionFullPairSumUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpCanonicalFunctionalReflectionFullPairSumUpTo X s := by
  rw [cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_totalSourceMass]
  exact cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo_nonneg X s

theorem cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo_nonneg
    (X : ℕ) (s : ℂ) :
    0 ≤ cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo X s := by
  rw [cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo_eq_squaredWeightDiagonal]
  exact cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo_nonneg X s

/-! The Mellin Gram kernel has spectral-node indices `(z,w)`.  The pair
kernel above has prime-power-label indices `(q,r)`; an identification of the
source-derived label feature with spectral nodes is outside this checkpoint. -/

inductive CfzpPrimeModePairToMellinSpectralGramBridgeGap : Prop
  | noSourceDerivedIndexFeatureIdentificationProvided

end DkMath.RH.CFBRCProjection
