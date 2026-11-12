/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyOrbitResonantLift

#print "file: DkMathTest.FLT.FreyResidueKernelOrbit"

-- A fixed vector can have a one-point orbit although the acting group is not cyclic.
example (n : ℤ) : n • ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) := by
  intro he
  have hs := congrArg Prod.snd he
  simp at hs

example {G : Type*} [Group G] (ρ : G →* Module.End ℤ (ZMod 2)) (φ : G) :
    ∀ σ : G, ∃ m : ℕ, ρ σ 0 = (ρ φ ^ m) 0 := by
  intro σ
  exact ⟨0, by simp⟩

#print axioms DkMath.FLT.Frey.Source.residueFieldAction
#print axioms DkMath.FLT.Frey.Source.residueFieldAction_ker
#print axioms DkMath.FLT.Frey.Source.residueFieldFaithfulAction
#print axioms DkMath.FLT.Frey.Source.residueFieldFaithfulAction_injective
#print axioms DkMath.FLT.Frey.Source.residueFieldAction_frobenius
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteResidueProjection
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteResidueProjection_comp
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteResidueProjection_surjective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.KernelOrbitGenerated
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelOrbitGenerated_of_finite_image
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelOrbitGenerated_frobenius_iff
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_orbit
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_frobenius_of_orbit
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_eigenvalue_of_orbit
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_orbit
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_orbit_sign
