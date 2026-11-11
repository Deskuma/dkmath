/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusDense
import DkMath.FLT.FreyResidualObstructionBranches

#print "file: DkMathTest.FLT.Note032ResidualFrobeniusBranchesAudit"

namespace Note032ResidualFrobeniusBranchesAudit

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
-- Traverse checked dependency graphs, including opaque proofs, for the three endpoints.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.frobeniusInertia_dense #[
    ``DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration.closure_eq_top_of_open_approximation,
    ``DkMath.FLT.Frey.Source.exists_frobenius_power_mod_open]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_plus_of_residual #[
    ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperClass_fixed_of_cofixed_p_torsion,
    ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.not_decomposition_fixed_of_residual_minus,
    ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_of_residual_plus]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_residual_plus #[
    ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_of_residual_plus,
    ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed]
  checkInputs ``DkMath.FLT.Frey.Source.frobeniusInertia_dense
    #[`A, `hA, `φ, `hφ] #[`hdense, `himage, `horbit, `hsign]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_plus_of_residual
    #[`h, `hp5, `hcofixed, `hres, `φ, `hφ] #[`hdense, `himage, `horbit, `hsign, `hclass]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_residual_plus
    #[`h, `hp5, `hcofixed, `hres, `hq1, `φ, `hφ] #[`hdense, `himage, `horbit, `hsign, `hclass]

end Note032ResidualFrobeniusBranchesAudit
