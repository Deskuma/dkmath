/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.TrivialCharacterH1
import DkMath.FLT.FreyFixedTameCharacter
import DkMath.FLT.FreyFixedInertiaH1
import DkMath.FLT.FreyInertiaH1CoefficientBoundary
#print "file: DkMathTest.FLT.Note032FreyFixedH1DependencyAudit"

namespace Note032FreyFixedH1DependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "P2M." || s.startsWith "P2MW." ||
    s.startsWith "FltRegular." || s.startsWith "FreyPackage." ||
    s.startsWith "DkMath.FLT.Kummer." || s.contains "fermatLastTheorem" ||
    s.contains "fermat_last_theorem" || s.contains "fermatFive_no_positive_solution"

private def checkRoot (root : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n then throwError "Forbidden dependency: {n}"
    let some info := env.checked.get.find? n | throwError "Missing constant: {n}"
    pending := pending ++ info.type.getUsedConstants
    if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  for n in required do
    unless visited.contains n do throwError "Required theorem absent: {n}"
  logInfo m!"PASS: {root}; {visited.size} reachable constants; required actual theorems present."

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | .letE n _ _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input absent in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; remaining arithmetic inputs explicit."

set_option maxHeartbeats 0 in
-- Every new production declaration: checked types, constructors and opaque values.
run_cmd do
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.coefficient #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.additive #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle #[``groupCohomology.cocycles₁IsoOfIsTrivial]
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle_apply #[``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle]
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cohomologyClass #[``groupCohomology.H1π]
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_evaluate #[``groupCohomology.H1IsoOfIsTrivial_H1π_apply_apply]
  checkRoot ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_ne_zero #[``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_evaluate]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_fixed_character_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_fixed_character_kernel, ``QuotientGroup.lift]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_mk #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_value #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameH1Class #[``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cohomologyClass, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaH1Class #[``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cohomologyClass, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_inflation_value #[``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_nontrivial #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero #[``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_ne_zero, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_nontrivial]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficient #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCocycle #[``groupCohomology.d₀₁_apply_mem_cocycles₁]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaClass_zero #[``groupCohomology.H1π_eq_zero_iff, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCocycle]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientInclusion #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedUpperQuotient, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficient]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_include_value #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaClass_map_zero #[``groupCohomology.H1π_comp_map_apply, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_include_value, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaClass_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_fixed_coefficient_H1 #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaClass_map_zero]
  checkInputs ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.coefficient #[`Γ, `V] #[`htrivial]
  checkInputs ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cocycle #[`f] #[`hcocycle]
  checkInputs ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.cohomologyClass #[`f] #[`hH1]
  checkInputs ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_ne_zero #[`f, `hf] #[`hH1]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_fixed_character_kernel #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameCharacter_continuous #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameH1Class #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaH1Class #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInertiaClass_map_zero #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficient #[`T, `A] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaClass_zero #[`T, `A, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientInclusion #[`T, `A] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_fixed_coefficient_H1 #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hH1, `hnonzero]

end Note032FreyFixedH1DependencyAudit
