/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyIntersectionQuotientObstruction

#print "file: DkMathTest.FLT.Note032FreyIntersectionQuotientDependencyAudit"

namespace Note032FreyIntersectionQuotientDependencyAudit

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
  checkRoot ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.intersectionKerEquiv #[]
  checkRoot ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.card_intersection_mul_image #[``DkMath.Lib.Algebra.FiniteSubgroupIntersection.intersectionKerEquiv, ``QuotientAddGroup.quotientKerEquivRange]
  checkRoot ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.prime_power_profile #[``DkMath.Lib.Algebra.FiniteSubgroupIntersection.card_intersection_mul_image]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.smoothIntersection #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.localComponentImage #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile #[``DkMath.Lib.Algebra.FiniteSubgroupIntersection.prime_power_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile_of_not_smooth #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperStage]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_finite #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.stable, ``QuotientAddGroup.map]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_order_eq_prime #[``addOrderOf_eq_prime_iff]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientAction]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.intersection_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile_of_not_smooth]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.difference_component_zero #[``DkMath.FLT.Frey.Source.mem_valuationSmoothSubgroup_iff]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.finite_quotient_witness #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_order_eq_prime, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_intersection_quotient_obstruction #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.intersection_profile, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.difference_component_zero, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.finite_quotient_witness]
  checkInputs ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.intersectionKerEquiv #[`K, `H] #[`hker]
  checkInputs ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.card_intersection_mul_image #[`K, `H] #[`hcard, `hfinite]
  checkInputs ``DkMath.Lib.Algebra.FiniteSubgroupIntersection.prime_power_profile #[`K, `H, `hp, `hcard] #[`hr, `hprofile]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile #[`T, `A] #[`hclass, `hbad, `hplacement, `hprofile]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.local_component_profile_of_not_smooth #[`T, `A, `hg] #[`hclass, `hbad, `hplacement, `hprofile]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_finite #[`T] #[`hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotientAction #[`T] #[`hclass, `hbad, `hcofixed, `hstable]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_order_eq_prime #[`T, `x, `hx, `hp] #[`horder]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed #[`T, `σ, `x, `hx] #[`hfixedQuotient]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.intersection_profile #[`h] #[`hclass, `hbad, `hprofile]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.difference_component_zero #[`h] #[`hclass, `hbad, `hcomponent]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.finite_quotient_witness #[`h] #[`hclass, `hbad, `horder, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_intersection_quotient_obstruction #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hbadAll, `hplacement, `hwitness, `hprofile, `horder]

end Note032FreyIntersectionQuotientDependencyAudit
