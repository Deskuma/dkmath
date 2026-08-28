/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedGramLimitRecoveryAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeGramSpecializationAudit"

/-!
# CFZP-006H: top-edge Gram specialization and dual-quadraticization boundary

The signed arithmetic Gram energy from CFZP-006F is specialized to the
symmetric rectangle top edge.  The signed half-width used here is
`1 / 2 - σ`, matching the existing rectangle orientation `σ..(1 - σ)`.

The resulting finite source norm-square average is folded to the finite
symmetric Euler rate and to the CFZP-006D ordered-pair ledger.  The legacy
continuous quadraticization audit is imported only to keep its contour-node /
vertical-amplitude semantics distinct from the arithmetic `± log q` family.

No completion remainder, linear Mellin density, off-diagonal sign, infinite
limit, or RH consequence is asserted.
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

/-! ## A. Top-edge center and signed half-width -/

def cfzpTopEdgeCenter (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalSymmetricRectangleTopEdge (1 / 2 : ℝ) W.rectangle.T

def cfzpTopEdgeHalfWidth (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  1 / 2 - W.rectangle.σ

theorem cfzpHorizontalRealShift_cfzpTopEdgeCenter
    (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) :
    cfzpHorizontalRealShift (cfzpTopEdgeCenter W) τ =
      pascalSymmetricRectangleTopEdge (1 / 2 + τ) W.rectangle.T := by
  unfold cfzpHorizontalRealShift cfzpTopEdgeCenter
    pascalSymmetricRectangleTopEdge
  apply Complex.ext <;> simp

theorem cfzpHorizontalRealShift_cfzpTopEdgeCenter_negHalfWidth
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpHorizontalRealShift (cfzpTopEdgeCenter W)
        (-cfzpTopEdgeHalfWidth W) =
      pascalSymmetricRectangleTopEdge W.rectangle.σ W.rectangle.T := by
  rw [cfzpHorizontalRealShift_cfzpTopEdgeCenter]
  unfold cfzpTopEdgeHalfWidth
  congr 1
  ring

theorem cfzpHorizontalRealShift_cfzpTopEdgeCenter_addHalfWidth
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpHorizontalRealShift (cfzpTopEdgeCenter W)
        (cfzpTopEdgeHalfWidth W) =
      pascalSymmetricRectangleTopEdge (1 - W.rectangle.σ) W.rectangle.T := by
  rw [cfzpHorizontalRealShift_cfzpTopEdgeCenter]
  unfold cfzpTopEdgeHalfWidth
  congr 1
  ring

/-! ## B. Full signed Gram on the complete top edge -/

noncomputable def cfzpTopEdgeFunctionalReflectionQuadraticEnergy
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
    (cfzpTopEdgeHalfWidth W) X (cfzpTopEdgeCenter W)

theorem cfzpTopEdgeFunctionalReflectionQuadraticEnergy_eq_topEdgeNormSqIntegral
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X =
      (2 * cfzpTopEdgeHalfWidth W)⁻¹ *
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          Complex.normSq
            (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
  unfold cfzpTopEdgeFunctionalReflectionQuadraticEnergy
  rw [cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_eq_shiftedSource_integral]
  congr 1
  calc
    (∫ τ in (-cfzpTopEdgeHalfWidth W)..cfzpTopEdgeHalfWidth W,
        Complex.normSq
          (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
            (cfzpHorizontalRealShift (cfzpTopEdgeCenter W) τ))) =
        ∫ τ in (-cfzpTopEdgeHalfWidth W)..cfzpTopEdgeHalfWidth W,
          Complex.normSq
            (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
              (pascalSymmetricRectangleTopEdge
                (1 / 2 + τ) W.rectangle.T)) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      change Complex.normSq
          (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
            (cfzpHorizontalRealShift (cfzpTopEdgeCenter W) τ)) =
        Complex.normSq
          (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
            (pascalSymmetricRectangleTopEdge (1 / 2 + τ) W.rectangle.T))
      rw [cfzpHorizontalRealShift_cfzpTopEdgeCenter]
    _ = ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          Complex.normSq
            (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
      convert (intervalIntegral.integral_comp_add_left
        (f := fun u : ℝ =>
          Complex.normSq
            (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)))
        (a := -cfzpTopEdgeHalfWidth W)
        (b := cfzpTopEdgeHalfWidth W) (d := (1 / 2 : ℝ))) using 1
      all_goals simp [cfzpTopEdgeHalfWidth]
      all_goals ring_nf

theorem cfzpTopEdgeFunctionalReflectionQuadraticEnergy_eq_topEdgeEulerRateNormSqIntegral
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X =
      (2 * cfzpTopEdgeHalfWidth W)⁻¹ *
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          Complex.normSq
            (pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
              (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
  rw [cfzpTopEdgeFunctionalReflectionQuadraticEnergy_eq_topEdgeNormSqIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  change Complex.normSq
      (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
    Complex.normSq
      (pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))
  rw [cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate]

/-! ## C. Pointwise source mass and ordered-pair ledger -/

theorem cfzpTopEdgeSourceNormSq_eq_totalSourceMass
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    Complex.normSq
        (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
      cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  rfl

theorem cfzpTopEdgeTotalSourceMass_eq_fullPairSum
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) :
    cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) =
      cfzpCanonicalFunctionalReflectionFullPairSumUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  exact (cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_totalSourceMass
    X (pascalSymmetricRectangleTopEdge u W.rectangle.T)).symm

theorem cfzpTopEdgeFunctionalReflectionQuadraticEnergy_eq_topEdgeFullPairSumIntegral
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X =
      (2 * cfzpTopEdgeHalfWidth W)⁻¹ *
        ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
          cfzpCanonicalFunctionalReflectionFullPairSumUpTo X
            (pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
  rw [cfzpTopEdgeFunctionalReflectionQuadraticEnergy_eq_topEdgeNormSqIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  change Complex.normSq
      (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) =
    cfzpCanonicalFunctionalReflectionFullPairSumUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)
  rw [cfzpTopEdgeSourceNormSq_eq_totalSourceMass W X u,
    cfzpTopEdgeTotalSourceMass_eq_fullPairSum W X u]

/-! ## D. Explicit semantic boundaries -/

inductive CfzpTopEdgeQuadraticMassToLinearMellinProjectionGap : Prop
  | noExactPolarizationBridgeProvided

inductive CfzpArithmeticSignedGramToLegacyContinuousQuadraticizationGap : Prop
  | noExactDualFeatureIdentificationProvided

end DkMath.RH.CFBRCProjection
