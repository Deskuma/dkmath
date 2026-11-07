/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationWildRigidity
import DkMath.Lib.RepresentationTheory.UnipotentDifferencePower
import DkMath.Lib.NumberTheory.EllipticWildRigidity
import DkMath.FLT.FreyWildInertia
#print "file: DkMathTest.FLT.Note032FreyWildInertiaDependencyAudit"

namespace Note032FreyWildInertiaDependencyAudit

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
-- Traverse checked types, constructors and opaque values for every new production declaration.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.valuation_lt_iff_div_mem_nonunits #[]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt #[]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.isWildAt_of_forall_mem_nonunits #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.valuation_lt_iff_div_mem_nonunits]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.valuation_apply #[]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.mul #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.valuation_apply]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.inv #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.valuation_apply]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.isWildAt_iff #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.isWildAt_of_forall_mem_nonunits]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.wildSubgroup #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.mul, ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.inv]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.pow #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.valuation_apply]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.fixed_of_unit_period #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.pow, ``Finset.sum_range_sub, ``Valuation.map_sum_lt]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.fixed_of_coprime_period #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.fixed_of_unit_period, ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd]
  checkRoot ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_pow #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.character]
  checkRoot ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.fixed_by_pow_of_killed #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_pow]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_fixed_of_wild_coprime_period #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.fixed_of_coprime_period]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_fixed_of_wild_coprime_period #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_fixed_of_wild_coprime_period]
  checkRoot ``DkMath.FLT.Frey.Source.wildInertiaSubgroup #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.wildSubgroup]
  checkRoot ``DkMath.FLT.Frey.Source.prime_power_wild_inertia_fixed #[``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.fixed_by_pow_of_killed, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_fixed_of_wild_coprime_period, ``DkMath.FLT.Frey.Source.prime_power_inertia_difference_product_zero]
  checkRoot ``DkMath.FLT.Frey.Source.frobenius_conjugate_error_wild #[``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_frob_conj]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel #[``DkMath.FLT.Frey.Source.prime_power_wild_inertia_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_frobenius_character_power #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel, ``DkMath.FLT.Frey.Source.frobenius_conjugate_error_wild, ``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_tame_inertia_character #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_frobenius_character_power]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationWildRigidity.wildSubgroup #[`A] #[]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.fixed_of_unit_period #[`A, `hw, `hm, `hy] #[`hq, `hfinite]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationWildRigidity.fixed_of_coprime_period #[`A, `hq, `hA, `hwild, `hm, `hy] #[`hfinite, `hproq]
  checkInputs ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.difference_pow #[`ρ, `hprod, `σ, `x, `m] #[`hperiod]
  checkInputs ``DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter.fixed_by_pow_of_killed #[`ρ, `hprod, `σ, `x, `hx] #[`hperiod]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_fixed_of_wild_coprime_period #[`E, `A, `hq, `hA, `σ, `hwild, `hm, `P, `hP] #[`hfinite, `hproq]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_fixed_of_wild_coprime_period #[`E, `A, `hq, `hA, `σ, `hwild, `hm, `x, `hx] #[`hfinite, `hproq]
  checkInputs ``DkMath.FLT.Frey.Source.wildInertiaSubgroup #[`A] #[`S, `hproq, `hwild]
  checkInputs ``DkMath.FLT.Frey.Source.prime_power_wild_inertia_fixed #[`S, `n, `hp5, `hq, `hqp, `haddr, `A, `hA, `σ, `hwild, `x] #[`hclass, `hbad, `hcofixed, `hperiod, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob]
  checkInputs ``DkMath.FLT.Frey.Source.frobenius_conjugate_error_wild #[`A, `hφ, `hτ] #[`hclass, `hwild, `hproq]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hperiod, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_frobenius_character_power #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hperiod, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_tame_inertia_character #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hperiod, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ]

end Note032FreyWildInertiaDependencyAudit
