/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInertiaH1CoefficientBoundary

#print "file: DkMathTest.FLT.FreyFixedCoefficientH1"

namespace FreyFixedCoefficientH1Test
open DkMath.Lib.RepresentationTheory
abbrev R := ZMod 5
abbrev Gamma := Multiplicative R
private def identityCharacter : Gamma →* Multiplicative R := MonoidHom.id _

-- A concrete nonzero ordinary H1 class with trivial coefficients, detected at the SAME value1.
example : TrivialCharacterH1.cohomologyClass identityCharacter ≠ 0 := by
  apply TrivialCharacterH1.class_ne_zero
  exact ⟨Multiplicative.ofAdd 1, by decide⟩
example : (groupCohomology.H1IsoOfIsTrivial (TrivialCharacterH1.coefficient Gamma R)).hom
    (TrivialCharacterH1.cohomologyClass identityCharacter) (Additive.ofMul (Multiplicative.ofAdd 1)) = 1 :=
  TrivialCharacterH1.class_evaluate identityCharacter _

-- The zero character gives a zero class; nontriviality is a necessary guard.
example : TrivialCharacterH1.cohomologyClass (1 : Gamma →* Multiplicative R) = 0 := by
  unfold TrivialCharacterH1.cohomologyClass
  have hz : TrivialCharacterH1.cocycle (1 : Gamma →* Multiplicative R) = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro g
    rfl
  rw [hz, map_zero]

private def shear (t : R) : Module.End R (R × R) where
  toFun x := (x.1 + t * x.2, x.2)
  map_add' x y := by
    apply Prod.ext
    · change x.1 + y.1 + t * (x.2 + y.2) = (x.1 + t * x.2) + (y.1 + t * y.2)
      ring
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · change c * x.1 + t * (c * x.2) = c * (x.1 + t * x.2)
      ring
    · rfl
private def rho : Representation R (Multiplicative R) (R × R) where
  toFun t := shear (Multiplicative.toAdd t)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp [shear]
  map_mul' t u := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change x.1 + (Multiplicative.toAdd t + Multiplicative.toAdd u) * x.2 =
        (x.1 + Multiplicative.toAdd u * x.2) + Multiplicative.toAdd t * x.2
      ring
    · rfl
private def rhoInt : Representation ℤ Gamma (R × R) where
  toFun g := (rho g).toAddMonoidHom.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : Module.End R (R × R) => f x) rho.map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : Module.End R (R × R) => f x) (rho.map_mul g h)
private def fullCoefficient : Rep ℤ Gamma := Rep.of rhoInt
private def boundaryCocycle : groupCohomology.cocycles₁ fullCoefficient :=
  ⟨groupCohomology.d₀₁ fullCoefficient (0, 1), groupCohomology.d₀₁_apply_mem_cocycles₁ _⟩

-- The SAME cochain has value(t,0) in the shear module, where it is a genuine coboundary.
example (t : R) : boundaryCocycle (Multiplicative.ofAdd t) = (t, 0) := by
  change ((0 : R) + t * 1 - 0, (1 : R) - 1) = (t, 0)
  simp only [zero_add, mul_one, sub_zero, sub_self]
example : groupCohomology.H1π fullCoefficient boundaryCocycle = 0 := by
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  exact ⟨(0, 1), rfl⟩
end FreyFixedCoefficientH1Test

#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.coefficient
#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.additive
#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle
#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle_apply
#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cohomologyClass
#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_evaluate
#print axioms DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_ne_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_fixed_character_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_value
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameH1Class
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaH1Class
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_inflation_value
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_nontrivial
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCocycle
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaClass_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientInclusion
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_include_value
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaClass_map_zero
#print axioms DkMath.FLT.Frey.Source.residual_exists_fixed_coefficient_H1
