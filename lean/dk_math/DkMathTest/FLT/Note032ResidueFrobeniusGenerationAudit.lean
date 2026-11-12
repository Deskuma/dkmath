/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusResonantLift

#print "file: DkMathTest.FLT.Note032ResidueFrobeniusGenerationAudit"

namespace Note032ResidueFrobeniusGenerationAudit

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
-- Traverse the full checked dependency graphs, including opaque proofs and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_frobenius #[
    ``DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure.residue_isAlgebraic,
    ``DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation.finite_values_pow,
    ``DkMath.Lib.RepresentationTheory.CompactFiniteDetection.exists_finite_detecting_set,
    ``DkMath.FLT.Frey.Source.exists_finite_residue_detection,
    ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_kernel_isOpen,
    ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_finiteDecompositionProjection_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_resonant_sign #[
    ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_frobenius,
    ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_frobenius
    #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `φ, `hφ] #[`himage, `horbit, `hdense, `hfactor, `hsign, `hD]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_resonant_sign
    #[`h, `hp5, `φ, `hφ, `hsign] #[`himage, `horbit, `hdense, `hfactor, `hD, `hclass, `hglobal, `hselmer]

end Note032ResidueFrobeniusGenerationAudit
