/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageIntersectionGenerator
import DkMath.FLT.FreyInertiaDifferenceCharacter

#print "file: DkMathTest.FLT.Note032FreyGeneratorCharacterDependencyAudit"

namespace Note032FreyGeneratorCharacterDependencyAudit

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
-- Inspect checked types, constructors and opaque proof values.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.zmultiples_generator #[]
  checkRoot ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order #[``DkMath.Lib.Algebra.CyclicIntersectionGenerator.zmultiples_generator]
  checkRoot ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order_prime_power #[``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order, ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.card_intersection_mul_image]
  checkRoot ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.intersection_eq_zmultiples #[``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order_prime_power, ``addOrderOf_nsmul_of_dvd]
  checkRoot ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_fixed #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_mul #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_fixed]
  checkRoot ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_mul]
  checkRoot ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_conjugate #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_generator_order #[``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.smooth_intersection_generator #[``DkMath.Lib.Algebra.CyclicIntersectionGenerator.intersection_eq_zmultiples]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_multiple_smooth_iff #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_generator_order]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_generator_profile_of_not_smooth #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile_of_not_smooth, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.smooth_intersection_generator, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_multiple_smooth_iff]
  checkRoot ``DkMath.FLT.Frey.Source.prime_power_inertia_difference_product_zero #[``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_product_zero, ``DkMath.FLT.Frey.Source.exists_geometry_at_bad_address]
  checkRoot ``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character, ``DkMath.FLT.Frey.Source.prime_power_inertia_difference_product_zero]
  checkRoot ``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_fixed #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter #[``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_apply #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_values_fixed #[``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_fixed, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_nontrivial_inertia_quotient_character #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial]
  checkInputs ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.zmultiples_generator #[`K, `e] #[`H, `hgenerator]
  checkInputs ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order #[`K, `H, `e] #[`horder]
  checkInputs ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.quotient_generator_order_prime_power #[`K, `H, `e, `hK, `hr, `hI] #[`horder]
  checkInputs ``DkMath.Lib.Algebra.CyclicIntersectionGenerator.intersection_eq_zmultiples #[`K, `H, `e, `hK, `hr, `hI] #[`hintersection]
  checkInputs ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_fixed #[`ρ, `hprod, `σ, `τ, `x] #[`hfixed]
  checkInputs ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character #[`ρ, `hprod, `x] #[`hchar, `hcocycle]
  checkInputs ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_conjugate #[`ρ, `φ, `τ, `x] #[`hprod, `hfrob, `hwild]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_multiple_smooth_iff #[`T, `A, `k] #[`hclass, `hbad, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_generator_profile_of_not_smooth #[`T, `A, `hg] #[`hclass, `hbad, `hplacement, `horder]
  checkInputs ``DkMath.FLT.Frey.Source.prime_power_inertia_difference_product_zero #[`S, `n, `hp5, `hq, `hqp, `haddr, `A, `hA, `σ, `τ] #[`hclass, `hbad, `hcofixed, `hprod, `hchar, `hwild, `hfrob]
  checkInputs ``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter #[`S, `n, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hprod, `hchar, `hwild, `hfrob]
  checkInputs ``DkMath.FLT.Frey.Source.inertiaDifferenceCharacter_fixed #[`S, `n, `hp5, `hq, `hqp, `haddr, `A, `hA, `σ, `τ, `x] #[`hclass, `hbad, `hcofixed, `hprod, `hchar, `hwild, `hfrob]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hprod, `hchar, `hwild, `hfrob]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_values_fixed #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x, `σ, `τ] #[`hclass, `hbad, `hcofixed, `hprod, `hchar, `hwild, `hfrob]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial #[`h, `hp5] #[`hclass, `hbad, `hchar, `horder]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_nontrivial_inertia_quotient_character #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hbadAll, `hplacement, `hchar, `horder, `hwild]

end Note032FreyGeneratorCharacterDependencyAudit
