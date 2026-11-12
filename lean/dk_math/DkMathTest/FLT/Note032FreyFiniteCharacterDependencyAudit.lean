/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FinitePrimePowerCharacter
import DkMath.FLT.FreyStageUpperQuotientCard
import DkMath.FLT.FreyStageUpperQuotientTopology
import DkMath.FLT.FreyInertiaCharacterFiniteImage
#print "file: DkMathTest.FLT.Note032FreyFiniteCharacterDependencyAudit"

namespace Note032FreyFiniteCharacterDependencyAudit

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
-- Checked types, constructors and opaque values, including all new production declarations.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.card_quotient_kernel #[``QuotientGroup.quotientKerEquivRange]
  checkRoot ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.image_profile #[``DkMath.Lib.Algebra.FinitePrimePowerCharacter.card_quotient_kernel, ``Subgroup.index_ker]
  checkRoot ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.nontrivial_image_profile #[``DkMath.Lib.Algebra.FinitePrimePowerCharacter.image_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStageEquiv #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage_card #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStageEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_card #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage_card, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientDiscreteTopology #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_orbit_continuous #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_orbit_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_action_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_orbit_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_continuous #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_orbit_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous #[``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_kernel_isClopen #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_apply]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedUpperQuotient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_values_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_apply #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_character_image_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_card, ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.image_profile]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_finite_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial, ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.nontrivial_image_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_kernel_isClopen]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_finite_inertia_character #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_finite_profile]
  checkInputs ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.card_quotient_kernel #[`f] #[]
  checkInputs ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.image_profile #[`f, `hp, `hA] #[`himage]
  checkInputs ``DkMath.Lib.Algebra.FinitePrimePowerCharacter.nontrivial_image_profile #[`f, `hp, `hA, `hf] #[`himage]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStageEquiv #[`T] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage_card #[`T] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_card #[`T] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_orbit_continuous #[`T, `z] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_action_continuous #[`T] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedUpperQuotient #[`T, `A] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_kernel_isClopen #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_character_image_profile #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_finite_profile #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_finite_inertia_character #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hcontinuous, `hfinite, `himage, `hindex, `hwild, `hfrob, `hplacement]

end Note032FreyFiniteCharacterDependencyAudit
