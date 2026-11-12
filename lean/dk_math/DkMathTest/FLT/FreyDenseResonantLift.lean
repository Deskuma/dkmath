/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseResonantLift

#print "file: DkMathTest.FLT.FreyDenseResonantLift"

section
local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

-- A closed subgroup containing a chosen element need not be the whole group.
-- This finite counterexample keeps the density premise necessary.
example : ∃ (H : Subgroup (Multiplicative (ZMod 2))) (φ : Multiplicative (ZMod 2)),
    IsClosed (H : Set (Multiplicative (ZMod 2))) ∧ φ ∈ H ∧ ∃ g, g ∉ H := by
  refine ⟨⊥, 1, ?_, Subgroup.one_mem _, Multiplicative.ofAdd 1, ?_⟩
  · simpa only [Subgroup.coe_bot] using
      (isClosed_singleton : IsClosed ({1} : Set (Multiplicative (ZMod 2))))
  · change Multiplicative.ofAdd (1 : ZMod 2) ≠ 1
    decide
end

-- The sign condition is an extra arithmetic fact even for an element of exact order p.
example : addOrderOf (1 : ZMod 5) = 5 ∧ 2 * (1 : ZMod 5) ≠ 1 ∧ 2 * (1 : ZMod 5) ≠ -1 :=
  ⟨ZMod.addOrderOf_one 5, by decide, by decide⟩

#print axioms DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.eq_top_of_dense_join
#print axioms DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.join_zpowers_eq_of_div_mem
#print axioms DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.linearStabilizer
#print axioms DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.fixed_of_dense_join
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer_isClosed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelClosedStabilizer
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_dense_join
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_of_dense_join
#print axioms DkMath.Lib.NumberTheory.ValuationFrobenius.residue_action_eq_of_frobenius
#print axioms DkMath.Lib.NumberTheory.ValuationFrobenius.frobenius_div_mem_inertia
#print axioms DkMath.FLT.Frey.Source.frobeniusResidueCoset_eq
#print axioms DkMath.FLT.Frey.Source.frobeniusInertiaJoin_eq
#print axioms DkMath.FLT.Frey.Source.frobeniusInertia_dense_iff
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFrobenius_action_eq
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientFrobenius_action_eq
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_action_eq
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_dense
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_dense
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_dense_sign
