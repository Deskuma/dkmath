/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionInvariantObstruction


#print "file: DkMathTest.FLT.FreyDecompositionEquivariance"

namespace FreyDecompositionEquivarianceTest
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : DkMath.FLT.Frey.Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

-- Actual old connecting equivalence is equivariant over the actual residue quotient.
example (s : (A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) (z : T.fixedQuotientCoefficient A) :
    T.kernelResidueAction A hp5 hq hqp haddr hA s (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA (T.quotientResidueAction A hp5 hq hqp haddr hA s z) :=
  T.quotientKernelEquiv_residue A hp5 hq hqp haddr hA s z

example (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    q • T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k) =
      T.fixedDecompositionAction A φ (T.fixedKernelEvaluation A τ k) :=
  T.kernelFrobenius_evaluation_relation A hp5 hq hqp haddr hA φ hφ τ k

-- Transport preserves a nonzero element, but does not imply invariance.
-- q=3, F-action by2 and K-action by4 satisfy the exact Frobenius covariance in ZMod5.
example : ∀ v : ZMod 5, 3 * (4 * v) = 2 * v := by decide
example : (1 : ZMod 5) ≠ 0 ∧ 4 * (1 : ZMod 5) ≠ 0 ∧ 4 * (1 : ZMod 5) ≠ 1 := by decide
example : ∀ v : ZMod 5, 2 * v = 3 * v ↔ v = 0 := by decide
example : ∀ x y : ZMod 5, 3 • x = 3 • y → x = y := by decide
end
end FreyDecompositionEquivarianceTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction_coset
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_decomposition
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction_coset
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionEvaluation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_generator_evaluation
#print axioms DkMath.FLT.Frey.Source.inertiaNormalInDecomposition
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_fixedDecomposition_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_quotientDecomposition_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelDecomposition_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedResidueAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientResidueAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelResidueAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_residue
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelEvaluation_frobenius_conjugate
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_evaluation_relation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixed_q_nsmul_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_fixed_iff
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_quotient_fixed
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_criterion
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.exists_frobenius_fixed_criterion
