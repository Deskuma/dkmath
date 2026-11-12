/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusDense
import DkMath.FLT.FreyResidualObstructionBranches

#print "file: DkMathTest.FLT.FreyResidualFrobeniusBranches"

local instance residualBranchesPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance residualBranchesPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The distinction between the two signs fails in characteristic two.
example : (1 : ZMod 2) = -1 := by decide

-- In contrast, the same separation lemma applies to a genuine order-five element.
example : (1 : ZMod 5) ≠ -1 := by
  apply DkMath.Lib.Algebra.PrimeOrderSignSeparation.ne_neg_of_order_gt_two
  rw [ZMod.addOrderOf_one]
  decide

#print axioms DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration.closed_eq_top_of_forall_open
#print axioms DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration.closure_eq_top_of_open_approximation
#print axioms DkMath.FLT.Frey.Source.frobeniusInertia_dense
#print axioms DkMath.FLT.Frey.Source.exists_frobeniusInertia_dense
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_eq_zero_of_base
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed_of_cofixed_p_torsion
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.GeneratorValueFromResidual
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_fixed_of_residual
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_of_residual_plus
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_not_from_base
#print axioms DkMath.Lib.Algebra.PrimeOrderSignSeparation.ne_neg_of_order_gt_two
#print axioms DkMath.Lib.Algebra.PrimeOrderSignSeparation.fixed_ne_neg_of_order_gt_two
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_not_neg_of_residual
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.not_decomposition_fixed_of_residual_minus
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_plus_of_residual
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_residual_plus
