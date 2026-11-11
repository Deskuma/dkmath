/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusResonantLift

#print "file: DkMathTest.FLT.FreyResidueFrobeniusGeneration"

local instance frobeniusGenerationPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

-- The approximation handles every automorphism of the four-element extension at once.
example (σ : GaloisField 2 2 ≃ₐ[ZMod 2] GaloisField 2 2) :
    ∃ m : ℕ, ∀ x : GaloisField 2 2, σ x = x ^ (2 ^ m) := by
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  obtain ⟨m, hm⟩ := DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation.finite_values_pow
    (ZMod 2) (GaloisField 2 2) σ Finset.univ
  exact ⟨m, fun x => by simpa using hm x (Finset.mem_univ x)⟩

#print axioms DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure.residue_isAlgClosed
#print axioms DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure.integral_residue_isAlgebraic
#print axioms DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure.residue_isAlgebraic
#print axioms DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure.residue_isAlgClosure
#print axioms DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation.finite_values_pow
#print axioms DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation.finite_values_frobenius
#print axioms DkMath.Lib.RepresentationTheory.CompactFiniteDetection.exists_finite_detecting_set
#print axioms DkMath.FLT.Frey.Source.residueFieldAlgAction
#print axioms DkMath.FLT.Frey.Source.residueFieldAlgAction_apply
#print axioms DkMath.FLT.Frey.Source.residueFinite_frobenius_approx
#print axioms DkMath.FLT.Frey.Source.decomposition_compact
#print axioms DkMath.FLT.Frey.Source.residue_moved_isOpen
#print axioms DkMath.FLT.Frey.Source.exists_finite_residue_detection
#print axioms DkMath.FLT.Frey.Source.exists_frobenius_power_mod_open
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_power_of_frobenius
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_frobenius
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelOrbitGenerated_of_frobenius
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_frobenius
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_resonant_sign
