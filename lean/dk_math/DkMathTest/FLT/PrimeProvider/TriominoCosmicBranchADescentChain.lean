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
