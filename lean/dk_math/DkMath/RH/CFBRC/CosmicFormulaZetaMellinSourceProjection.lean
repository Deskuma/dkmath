/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedSourceRecoveryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection"

/-!
# CFZP-005: Mellin and functional-reflection source projection

This module transports the finite canonical prime-power source to the
functional-reflection CS37/CS38 source channel.  The reflection here is
`s ↦ 1 - s`, which reverses the cycle height; it is deliberately distinct
from CFZP-004's same-height `criticalMirror`.

The Euler source is linear and signed.  It is not identified with the
nonnegative quadratic Gap ledger.  The full projected mirror density retains
the completed-zeta and Gamma channels before the oriented half-integral is
recovered.

No rectangle completion Gap, infinite product, phase branch, or RH statement
is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## Functional-reflection mode source -/

/-- The signed functional-reflection difference of one natural mode. -/
noncomputable def cfzpFunctionalReflectionModeDifference
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-(1 - s)) - (q : ℂ) ^ (-s)

theorem cfzpFunctionalReflectionModeDifference_eq_commonRadial_mul_phaseDisplacedAmplitude
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpFunctionalReflectionModeDifference q s =
      cfzpPrimePowerCommonRadialCarrier q *
        ((primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q (-s.im) -
          (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q s.im) := by
  unfold cfzpFunctionalReflectionModeDifference
  rw [natCpowNeg_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle hq s,
    natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle hq s]
  ring

/-! ## Canonical finite functional-reflection source -/

noncomputable def cfzpCanonicalFunctionalReflectionLinearSourceUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q : ℂ) *
      cfzpFunctionalReflectionModeDifference q s

theorem cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X (1 - s) -
        pascalPrimePowerPHZCanonicalUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionLinearSourceUpTo
    cfzpFunctionalReflectionModeDifference
  rw [pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
      pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s := by
  calc
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
        pascalPrimePowerPHZCanonicalUpTo X (1 - s) -
          pascalPrimePowerPHZCanonicalUpTo X s :=
      cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference
        X s
    _ = pascalPrimePowerPHZFiniteUpTo X (1 - s) -
          pascalPrimePowerPHZFiniteUpTo X s := by
      rw [← pascalPrimePowerPHZFiniteUpTo_eq_canonical,
        ← pascalPrimePowerPHZFiniteUpTo_eq_canonical]
    _ = pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s := by
      rfl

/-! ## Existing top Mellin weight and CS38 Euler channel -/

noncomputable def cfzpFiniteMellinSymmetricEulerDensity
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im

theorem cfzpFiniteMellinSymmetricEulerDensity_eq_cs38
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerDensity ε X W u =
      pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerDensity
    pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity
  rw [cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate]

/-! ## Full CS38 projected density -/

noncomputable def cfzpProjectedMirrorScalarDensity
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity ε W u +
    pascalCenteredXiPrimeSideFiniteGammaMirrorDensity ε W u +
      cfzpFiniteMellinSymmetricEulerDensity ε X W u

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_eq_cfzpProjected
    {ε : ℝ}
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u =
      cfzpProjectedMirrorScalarDensity ε X W u := by
  calc
    pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u =
        pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity ε W u +
          pascalCenteredXiPrimeSideFiniteGammaMirrorDensity ε W u +
            pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity ε X W u :=
      pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_eq_weighted_functionalEquation_channels
        hSafe hu
    _ = cfzpProjectedMirrorScalarDensity ε X W u := by
      unfold cfzpProjectedMirrorScalarDensity
      rw [cfzpFiniteMellinSymmetricEulerDensity_eq_cs38]

/-! ## Oriented half-interval source recovery -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_cfzpProjected_half_integral
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
          cfzpProjectedMirrorScalarDensity ε X W u := by
  have hbase :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_mirror_weighted_half_integral
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  rw [hbase]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  apply pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_eq_cfzpProjected
    hSafe
  have hhalf : (1 / 2 : ℝ) ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  rw [Set.uIcc_of_ge hσ]
  rw [Set.uIcc_of_ge hhalf] at hu
  constructor
  · linarith [hu.1]
  · exact hu.2

end DkMath.RH.CFBRCProjection
