/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResonantDecompositionLift

#print "file: DkMathTest.FLT.FreyResonantDecompositionLift"

-- The resonance scalar identity does not supply an eigenvalue of the actual F action.
example : ∀ v : ZMod 5, 11 • v = v := by decide
example : ∀ v : ZMod 5, 19 • v = -v := by decide
example : ∃ v : ZMod 5, v ≠ 0 ∧ 2 * v ≠ v ∧ 2 * v ≠ -v := by decide

#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_order_eq_prime
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_nsmul_mod
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_plus
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_minus
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_resonant_signs
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficientTopology
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficientDiscrete
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficientTopology
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficientDiscrete
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecomposition_orbit_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecomposition_orbit_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isClosed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionCoefficientTopology
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullDecompositionCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientInclusion
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientProjection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence_shortExact
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnecting
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCosetH0
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_difference_mem_fixed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_class
#print axioms DkMath.FLT.Frey.Source.inertiaToDecomposition
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionInertiaCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionInertiaRestriction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCocycle_restrict
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionClass_restrict_kernel
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.exists_prime_sign_frobenius_criterion
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed
