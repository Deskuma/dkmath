/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeGramSpecializationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeWeightedPolarizationAudit"

/-!
# CFZP-006I: top-edge weighted polarization

The finite Mellin weight and the finite functional-reflection source are
packaged as one complex source.  Multiplication by `-I` changes its real
coordinate to the CFZP-005 Euler density without changing its norm-square.
The two translated square masses then recover the density by their
difference and the weighted quadratic mass by their sum.

All statements are finite and pointwise.  This file does not identify any
of these quantities with a completion remainder, a zeta mismatch, a legacy
quadraticization, an infinite product, or an RH statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. The weighted Euler complex source -/

noncomputable def cfzpFiniteMellinSymmetricEulerComplexSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)

theorem cfzpFiniteMellinSymmetricEulerComplexSource_im
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    (cfzpFiniteMellinSymmetricEulerComplexSource ε X W u).im =
      cfzpFiniteMellinSymmetricEulerDensity ε X W u := by
  rfl

theorem cfzpFiniteMellinSymmetricEulerComplexSource_eq_weight_mul_eulerRate
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerComplexSource ε X W u =
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
        pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  unfold cfzpFiniteMellinSymmetricEulerComplexSource
  rw [cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate]

/-! ## B. Deorientation -/

noncomputable def cfzpFiniteMellinSymmetricEulerDeorientedSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℂ :=
  -Complex.I * cfzpFiniteMellinSymmetricEulerComplexSource ε X W u

theorem cfzpFiniteMellinSymmetricEulerDeorientedSource_re
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u).re =
      cfzpFiniteMellinSymmetricEulerDensity ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerDeorientedSource
    cfzpFiniteMellinSymmetricEulerComplexSource
    cfzpFiniteMellinSymmetricEulerDensity
  simp [Complex.mul_re]

theorem cfzpFiniteMellinSymmetricEulerDeorientedSource_normSq
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    Complex.normSq (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u) =
      Complex.normSq (cfzpFiniteMellinSymmetricEulerComplexSource ε X W u) := by
  unfold cfzpFiniteMellinSymmetricEulerDeorientedSource
  rw [Complex.normSq_mul]
  simp [Complex.normSq_apply]

/-! ## C. Weighted quadratic mass -/

noncomputable def cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Complex.normSq (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u)

theorem cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass_nonneg
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    0 ≤ cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass
  exact Complex.normSq_nonneg _

theorem cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass_eq_weight_mul_totalSourceMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass ε X W u =
      Complex.normSq
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u) *
        cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  rw [cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass,
    cfzpFiniteMellinSymmetricEulerDeorientedSource_normSq]
  unfold cfzpFiniteMellinSymmetricEulerComplexSource
    cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo
  rw [Complex.normSq_mul]

theorem cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass_eq_weight_mul_fullPairSum
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass ε X W u =
      Complex.normSq
          (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u) *
        cfzpCanonicalFunctionalReflectionFullPairSumUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  rw [cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass_eq_weight_mul_totalSourceMass]
  rw [cfzpTopEdgeTotalSourceMass_eq_fullPairSum]

/-! ## D. Two nonnegative polarized masses -/

noncomputable def cfzpFiniteMellinSymmetricEulerPolarizedPlusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Complex.normSq
    (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u + 1)

noncomputable def cfzpFiniteMellinSymmetricEulerPolarizedMinusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Complex.normSq
    (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u - 1)

theorem cfzpFiniteMellinSymmetricEulerPolarizedPlusMass_nonneg
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    0 ≤ cfzpFiniteMellinSymmetricEulerPolarizedPlusMass ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerPolarizedPlusMass
  exact Complex.normSq_nonneg _

theorem cfzpFiniteMellinSymmetricEulerPolarizedMinusMass_nonneg
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    0 ≤ cfzpFiniteMellinSymmetricEulerPolarizedMinusMass ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerPolarizedMinusMass
  exact Complex.normSq_nonneg _

private theorem complex_normSq_add_one_sub_normSq_sub_one (z : ℂ) :
    Complex.normSq (z + 1) - Complex.normSq (z - 1) = 4 * z.re := by
  simp [Complex.normSq_apply]
  ring

private theorem complex_normSq_add_one_add_normSq_sub_one (z : ℂ) :
    Complex.normSq (z + 1) + Complex.normSq (z - 1) =
      2 * (Complex.normSq z + 1) := by
  simp [Complex.normSq_apply]
  ring

theorem cfzpFiniteMellinSymmetricEulerPolarizedMass_difference
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerPolarizedPlusMass ε X W u -
        cfzpFiniteMellinSymmetricEulerPolarizedMinusMass ε X W u =
      4 * cfzpFiniteMellinSymmetricEulerDensity ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerPolarizedPlusMass
    cfzpFiniteMellinSymmetricEulerPolarizedMinusMass
  rw [complex_normSq_add_one_sub_normSq_sub_one,
    cfzpFiniteMellinSymmetricEulerDeorientedSource_re]

theorem cfzpFiniteMellinSymmetricEulerDensity_eq_polarizedMass_difference_div_four
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerDensity ε X W u =
      (cfzpFiniteMellinSymmetricEulerPolarizedPlusMass ε X W u -
        cfzpFiniteMellinSymmetricEulerPolarizedMinusMass ε X W u) / 4 := by
  rw [cfzpFiniteMellinSymmetricEulerPolarizedMass_difference]
  ring

theorem cfzpFiniteMellinSymmetricEulerPolarizedMass_sum
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerPolarizedPlusMass ε X W u +
        cfzpFiniteMellinSymmetricEulerPolarizedMinusMass ε X W u =
      2 * (cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass ε X W u + 1) := by
  unfold cfzpFiniteMellinSymmetricEulerPolarizedPlusMass
    cfzpFiniteMellinSymmetricEulerPolarizedMinusMass
  rw [complex_normSq_add_one_add_normSq_sub_one,
    cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass]

theorem cfzpFiniteMellinSymmetricEulerPolarizedPlusMass_eq_weightedQuadraticMass_add_one_add_density
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerPolarizedPlusMass ε X W u =
      cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass ε X W u + 1 +
        2 * cfzpFiniteMellinSymmetricEulerDensity ε X W u := by
  have hdiff := cfzpFiniteMellinSymmetricEulerPolarizedMass_difference ε X W u
  have hsum := cfzpFiniteMellinSymmetricEulerPolarizedMass_sum ε X W u
  linarith

theorem cfzpFiniteMellinSymmetricEulerPolarizedMinusMass_eq_weightedQuadraticMass_add_one_sub_density
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerPolarizedMinusMass ε X W u =
      cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass ε X W u + 1 -
        2 * cfzpFiniteMellinSymmetricEulerDensity ε X W u := by
  have hdiff := cfzpFiniteMellinSymmetricEulerPolarizedMass_difference ε X W u
  have hsum := cfzpFiniteMellinSymmetricEulerPolarizedMass_sum ε X W u
  linarith

/-! ## E. Pointwise balance frontier -/

theorem cfzpFiniteMellinSymmetricEulerPolarizedMass_balance_iff_density_eq_zero
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerPolarizedPlusMass ε X W u =
        cfzpFiniteMellinSymmetricEulerPolarizedMinusMass ε X W u ↔
      cfzpFiniteMellinSymmetricEulerDensity ε X W u = 0 := by
  rw [← sub_eq_zero]
  rw [cfzpFiniteMellinSymmetricEulerPolarizedMass_difference]
  constructor
  · intro h
    linarith
  · intro h
    linarith

inductive CfzpWeightedPolarizationBalanceToSourceZeroGap : Prop
  | noExactComplexSourceZeroIdentificationProvided

end DkMath.RH.CFBRCProjection
