/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeWeightedPolarizationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaProjectedMirrorPolarizationAudit"

/-!
# CFZP-006J: projected mirror three-channel polarization

The completed, Gamma, and Euler channels are packaged into one finite
weighted complex source.  Its deoriented real coordinate is the projected
mirror scalar density from CFZP-005.  The two translated square masses give
the density by their difference and the total projected quadratic mass by
their sum.

The TopMismatch recovery below preserves the existing reverse-oriented
half-interval and its hypotheses.  No channel cross term is discarded, and
no projected quadratic mass is identified with the Euler-only FullPairSum or
with a completion remainder.
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

/-! ## A. Completed / Gamma / Euler complex channels -/

noncomputable def cfzpFiniteMellinCompletedMirrorComplexSource
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteCompletedZetaMirrorRate
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)

noncomputable def cfzpFiniteMellinGammaMirrorComplexSource
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    pascalCenteredXiPrimeSideFiniteGammaMirrorRate
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)

noncomputable def cfzpProjectedMirrorComplexSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  cfzpFiniteMellinCompletedMirrorComplexSource ε W u +
    cfzpFiniteMellinGammaMirrorComplexSource ε W u +
      cfzpFiniteMellinSymmetricEulerComplexSource ε X W u

theorem cfzpProjectedMirrorComplexSource_eq_channel_sum
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorComplexSource ε X W u =
      cfzpFiniteMellinCompletedMirrorComplexSource ε W u +
        cfzpFiniteMellinGammaMirrorComplexSource ε W u +
          cfzpFiniteMellinSymmetricEulerComplexSource ε X W u := by
  rfl

theorem cfzpProjectedMirrorComplexSource_im
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    (cfzpProjectedMirrorComplexSource ε X W u).im =
      cfzpProjectedMirrorScalarDensity ε X W u := by
  unfold cfzpProjectedMirrorComplexSource
    cfzpFiniteMellinCompletedMirrorComplexSource
    cfzpFiniteMellinGammaMirrorComplexSource
    cfzpFiniteMellinSymmetricEulerComplexSource
    cfzpProjectedMirrorScalarDensity
    cfzpFiniteMellinSymmetricEulerDensity
    pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity
    pascalCenteredXiPrimeSideFiniteGammaMirrorDensity
  simp only [Complex.add_im]

/-! ## B. Total deorientation -/

noncomputable def cfzpProjectedMirrorDeorientedSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  -Complex.I * cfzpProjectedMirrorComplexSource ε X W u

theorem cfzpProjectedMirrorDeorientedSource_re
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    (cfzpProjectedMirrorDeorientedSource ε X W u).re =
      cfzpProjectedMirrorScalarDensity ε X W u := by
  unfold cfzpProjectedMirrorDeorientedSource
  simp [Complex.mul_re, cfzpProjectedMirrorComplexSource_im]

theorem cfzpProjectedMirrorDeorientedSource_normSq
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    Complex.normSq (cfzpProjectedMirrorDeorientedSource ε X W u) =
      Complex.normSq (cfzpProjectedMirrorComplexSource ε X W u) := by
  unfold cfzpProjectedMirrorDeorientedSource
  rw [Complex.normSq_mul]
  simp [Complex.normSq_apply]

theorem cfzpProjectedMirrorDeorientedSource_eq_channel_sum
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorDeorientedSource ε X W u =
      (-Complex.I * cfzpFiniteMellinCompletedMirrorComplexSource ε W u) +
        (-Complex.I * cfzpFiniteMellinGammaMirrorComplexSource ε W u) +
          (-Complex.I * cfzpFiniteMellinSymmetricEulerComplexSource ε X W u) := by
  unfold cfzpProjectedMirrorDeorientedSource
    cfzpProjectedMirrorComplexSource
  ring

/-! ## C. Total projected quadratic mass -/

noncomputable def cfzpProjectedMirrorWeightedQuadraticMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  Complex.normSq (cfzpProjectedMirrorDeorientedSource ε X W u)

theorem cfzpProjectedMirrorWeightedQuadraticMass_nonneg
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    0 ≤ cfzpProjectedMirrorWeightedQuadraticMass ε X W u := by
  unfold cfzpProjectedMirrorWeightedQuadraticMass
  exact Complex.normSq_nonneg _

/-! ## D. Two projected nonnegative masses -/

noncomputable def cfzpProjectedMirrorPolarizedPlusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  Complex.normSq (cfzpProjectedMirrorDeorientedSource ε X W u + 1)

noncomputable def cfzpProjectedMirrorPolarizedMinusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  Complex.normSq (cfzpProjectedMirrorDeorientedSource ε X W u - 1)

theorem cfzpProjectedMirrorPolarizedPlusMass_nonneg
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    0 ≤ cfzpProjectedMirrorPolarizedPlusMass ε X W u := by
  unfold cfzpProjectedMirrorPolarizedPlusMass
  exact Complex.normSq_nonneg _

theorem cfzpProjectedMirrorPolarizedMinusMass_nonneg
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    0 ≤ cfzpProjectedMirrorPolarizedMinusMass ε X W u := by
  unfold cfzpProjectedMirrorPolarizedMinusMass
  exact Complex.normSq_nonneg _

private theorem cfzpProjected_normSq_add_one_sub_normSq_sub_one (z : ℂ) :
    Complex.normSq (z + 1) - Complex.normSq (z - 1) = 4 * z.re := by
  simp [Complex.normSq_apply]
  ring

private theorem cfzpProjected_normSq_add_one_add_normSq_sub_one (z : ℂ) :
    Complex.normSq (z + 1) + Complex.normSq (z - 1) =
      2 * (Complex.normSq z + 1) := by
  simp [Complex.normSq_apply]
  ring

theorem cfzpProjectedMirrorPolarizedMass_difference
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorPolarizedPlusMass ε X W u -
        cfzpProjectedMirrorPolarizedMinusMass ε X W u =
      4 * cfzpProjectedMirrorScalarDensity ε X W u := by
  unfold cfzpProjectedMirrorPolarizedPlusMass
    cfzpProjectedMirrorPolarizedMinusMass
  rw [cfzpProjected_normSq_add_one_sub_normSq_sub_one,
    cfzpProjectedMirrorDeorientedSource_re]

theorem cfzpProjectedMirrorPolarizedMass_sum
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorPolarizedPlusMass ε X W u +
        cfzpProjectedMirrorPolarizedMinusMass ε X W u =
      2 * (cfzpProjectedMirrorWeightedQuadraticMass ε X W u + 1) := by
  unfold cfzpProjectedMirrorPolarizedPlusMass
    cfzpProjectedMirrorPolarizedMinusMass
  rw [cfzpProjected_normSq_add_one_add_normSq_sub_one,
    cfzpProjectedMirrorWeightedQuadraticMass]

theorem cfzpProjectedMirrorPolarizedPlusMass_eq_quadraticMass_add_one_add_density
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorPolarizedPlusMass ε X W u =
      cfzpProjectedMirrorWeightedQuadraticMass ε X W u + 1 +
        2 * cfzpProjectedMirrorScalarDensity ε X W u := by
  have hdiff := cfzpProjectedMirrorPolarizedMass_difference ε X W u
  have hsum := cfzpProjectedMirrorPolarizedMass_sum ε X W u
  linarith

theorem cfzpProjectedMirrorPolarizedMinusMass_eq_quadraticMass_add_one_sub_density
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorPolarizedMinusMass ε X W u =
      cfzpProjectedMirrorWeightedQuadraticMass ε X W u + 1 -
        2 * cfzpProjectedMirrorScalarDensity ε X W u := by
  have hdiff := cfzpProjectedMirrorPolarizedMass_difference ε X W u
  have hsum := cfzpProjectedMirrorPolarizedMass_sum ε X W u
  linarith

/-! ## E. Pointwise balance frontier -/

theorem cfzpProjectedMirrorPolarizedMass_balance_iff_density_eq_zero
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzpProjectedMirrorPolarizedPlusMass ε X W u =
        cfzpProjectedMirrorPolarizedMinusMass ε X W u ↔
      cfzpProjectedMirrorScalarDensity ε X W u = 0 := by
  rw [← sub_eq_zero]
  rw [cfzpProjectedMirrorPolarizedMass_difference]
  constructor
  · intro h
    linarith
  · intro h
    linarith

inductive CfzpProjectedPolarizationBalanceToComplexSourceZeroGap : Prop
  | noExactComplexSourceZeroIdentificationProvided

/-! ## F. Existing TopMismatch recovery, rewritten by polarization -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_projectedPolarized_half_integral
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (1 / Real.pi) *
        ∫ u in W.rectangle.σ..(1 / 2 : ℝ),
          (cfzpProjectedMirrorPolarizedPlusMass ε X W u -
            cfzpProjectedMirrorPolarizedMinusMass ε X W u) / 4 := by
  have hbase :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_cfzpProjected_half_integral
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  rw [hbase]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  change cfzpProjectedMirrorScalarDensity ε X W u =
    (cfzpProjectedMirrorPolarizedPlusMass ε X W u -
      cfzpProjectedMirrorPolarizedMinusMass ε X W u) / 4
  rw [cfzpProjectedMirrorPolarizedMass_difference]
  ring

/-! The reverse orientation is retained; no integrated nonnegativity is
claimed for the two separately oriented terms. -/

inductive CfzpProjectedChannelQuadraticAdditivityGap : Prop
  | crossChannelInterferenceNotDiscarded

end DkMath.RH.CFBRCProjection
