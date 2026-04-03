/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchADescentChain

#print "file: DkMathTest.FLT.PrimeProvider.TriominoCosmicBranchADescentChain"

set_option linter.style.whitespace false
set_option linter.style.longLine false

#print axioms DkMath.FLT.superWieferichCongruence_concrete
-- OK: 2026/04/03 17:55
-- 'DkMath.FLT.superWieferichCongruence_concrete'
-- depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms DkMath.FLT.weakSuperWieferich_of_strong
-- OK: 2026/04/03 18:14
-- 'DkMath.FLT.weakSuperWieferich_of_strong'
-- depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms DkMath.FLT.weakSuperWieferich_of_strongV2
-- OK: 2026/04/03 18:39
-- 'DkMath.FLT.weakSuperWieferich_of_strongV2'
-- depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms DkMath.FLT.henselLiftStepStructural_concrete
-- OK: 2026/04/03 18:59
-- 'DkMath.FLT.henselLiftStepStructural_concrete'
-- depends on axioms: [propext, Quot.sound]
#print axioms DkMath.FLT.henselLiftStepGeomSum_of_structural_and_kernel
-- OK: 2026/04/03 18:59
-- 'DkMath.FLT.henselLiftStepGeomSum_of_structural_and_kernel'
-- depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms DkMath.FLT.henselLiftStepArithmeticKernel_of_correction
-- OK: 2026/04/03 19:19
-- 'DkMath.FLT.henselLiftStepArithmeticKernel_of_correction'
-- depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms DkMath.FLT.henselLiftStepCorrection_of_zeroLift  -- OK
#print axioms DkMath.FLT.henselLiftStepArithmeticKernel_of_zeroLift  -- OK
#print axioms DkMath.FLT.henselLiftStepGeomSum_of_zeroLift  -- OK
#print axioms DkMath.FLT.qpow_mul_sq_eq_zero_in_next_mod -- OK
#print axioms DkMath.FLT.castHom_qpow_mul_eq_zero -- OK
#print axioms DkMath.FLT.geomSum_first_order_qpow_correction -- OK
#print axioms DkMath.FLT.geomSumFirstOrderSqZero_concrete -- OK
#print axioms DkMath.FLT.geomSum_first_order_qpow_correction_concrete -- OK
#print axioms DkMath.FLT.henselLiftStepNewtonCorrection_of_linearizedSolve -- OK
#print axioms DkMath.FLT.henselLiftStepLinearizedSolve_of_kernelDivision_and_derivativeUnit -- OK
#print axioms DkMath.FLT.henselLiftStepKernelDivision_concrete -- OK
#print axioms DkMath.FLT.henselLiftStepLinearizedSolve_of_derivativeUnit -- OK
#print axioms DkMath.FLT.isUnit_of_nonzero_mod_q_primepow -- OK
#print axioms DkMath.FLT.henselLiftStepDerivativeUnitPrime_of_nonzeroModQ -- OK
#print axioms DkMath.FLT.henselLiftStepLinearizedSolve_of_nonzeroModQ_prime -- OK
#print axioms DkMath.FLT.henselLiftStepZeroLift_of_newtonCorrection -- OK
#print axioms DkMath.FLT.henselLiftStepZeroLift_of_nonzeroModQ_prime -- OK
#print axioms DkMath.FLT.henselLiftStepCorrection_of_nonzeroModQ_prime -- OK
#print axioms DkMath.FLT.henselLiftStepArithmeticKernel_of_nonzeroModQ_prime -- OK
#print axioms DkMath.FLT.henselLiftStepGeomSum_of_nonzeroModQ_prime -- OK
#print axioms DkMath.FLT.strongSuperWieferichCongruenceV2_concrete -- OK
#print axioms DkMath.FLT.strongSuperWieferichProvider_concrete -- OK
#print axioms DkMath.FLT.pthRootCore_of_qAdicDescentExistence -- OK
#print axioms DkMath.FLT.pthRoot_of_qAdicDescentExistence -- OK
#print axioms DkMath.FLT.gnReducedGap_of_qAdicDescentExistence -- OK
#print axioms DkMath.FLT.primitivePacketDescent_of_qAdicDescentExistence -- OK
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_qAdicDescentExistence_precise -- OK
#print axioms DkMath.FLT.qAdicLocalGlobalGap_of_qAdicDescentExistence -- OK
#print axioms DkMath.FLT.qAdicGapReduction_of_qAdicLocalGlobalGap -- OK
#print axioms DkMath.FLT.qAdicLocalGlobalGap_of_qAdicGapReduction -- OK
#print axioms DkMath.FLT.pthRootCore_of_qAdicLocalGlobalGap -- OK
#print axioms DkMath.FLT.pthRootCore_of_qAdicGapReduction -- OK
#print axioms DkMath.FLT.pthRoot_of_qAdicLocalGlobalGap -- OK
#print axioms DkMath.FLT.gnReducedGap_of_qAdicLocalGlobalGap -- OK
#print axioms DkMath.FLT.primitivePacketDescent_of_qAdicLocalGlobalGap -- OK
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_qAdicLocalGlobalGap_precise -- OK
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_qAdicGapReduction_precise -- OK
