/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseResonantLift

#print "file: DkMathTest.FLT.Note032DenseResonantLiftAudit"

namespace Note032DenseResonantLiftAudit

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
-- Each root traverses the full checked graph, including opaque proofs, types and constructors.
run_cmd do
  checkRoot ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.eq_top_of_dense_join #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.join_zpowers_eq_of_div_mem #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.linearStabilizer #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.fixed_of_dense_join #[``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.eq_top_of_dense_join, ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.linearStabilizer]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer #[``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.linearStabilizer]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer_isClosed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isClosed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelClosedStabilizer #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelDecomposition_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_dense_join #[``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.eq_top_of_dense_join, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer_isClosed, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelClosedStabilizer]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_of_dense_join #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_dense_join]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationFrobenius.residue_action_eq_of_frobenius #[]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationFrobenius.frobenius_div_mem_inertia #[``DkMath.Lib.NumberTheory.ValuationFrobenius.residue_action_eq_of_frobenius]
  checkRoot ``DkMath.FLT.Frey.Source.frobeniusResidueCoset_eq #[``DkMath.Lib.NumberTheory.ValuationFrobenius.frobenius_div_mem_inertia]
  checkRoot ``DkMath.FLT.Frey.Source.frobeniusInertiaJoin_eq #[``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.join_zpowers_eq_of_div_mem, ``DkMath.Lib.NumberTheory.ValuationFrobenius.frobenius_div_mem_inertia]
  checkRoot ``DkMath.FLT.Frey.Source.frobeniusInertia_dense_iff #[``DkMath.FLT.Frey.Source.frobeniusInertiaJoin_eq]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFrobenius_action_eq #[``DkMath.FLT.Frey.Source.frobeniusResidueCoset_eq, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedResidueAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientFrobenius_action_eq #[``DkMath.FLT.Frey.Source.frobeniusResidueCoset_eq, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientResidueAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_action_eq #[``DkMath.FLT.Frey.Source.frobeniusResidueCoset_eq, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelResidueAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_dense #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_of_dense_join, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_fixed_iff]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_dense #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_dense, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_plus, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_minus]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_dense_sign #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_dense, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed]
  checkInputs ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.eq_top_of_dense_join #[`N, `H, `φ, `hclosed, `hN, `hφ, `hdense] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.join_zpowers_eq_of_div_mem #[`N, `φ, `ψ, `h] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.linearStabilizer #[`ρ, `m] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.fixed_of_dense_join #[`ρ, `m, `N, `φ, `hclosed, `hN, `hφ, `hdense] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelClosedStabilizer_isClosed #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelClosedStabilizer #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_dense_join #[`T, `A, `hdense, `hfixed] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_of_dense_join #[`T, `A, `hdense] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationFrobenius.residue_action_eq_of_frobenius #[`A, `φ, `ψ, `hφ, `hψ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationFrobenius.frobenius_div_mem_inertia #[`A, `φ, `ψ, `hφ, `hψ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.frobeniusResidueCoset_eq #[`A, `φ, `ψ, `hφ, `hψ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.frobeniusInertiaJoin_eq #[`A, `φ, `ψ, `hφ, `hψ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.frobeniusInertia_dense_iff #[`A, `φ, `ψ, `hφ, `hψ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFrobenius_action_eq #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientFrobenius_action_eq #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_action_eq #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_dense #[`T, `A, `hdense] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_dense #[`h, `hp5, `φ, `hφ, `hdense] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_dense_sign #[`h, `hp5, `φ, `hφ, `hdense, `hsign] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect]

end Note032DenseResonantLiftAudit
