/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRelativeGlobalObstructionCertificate

#print "file: DkMathTest.FLT.Note032RelativeOriginDependencyAudit"

namespace Note032RelativeOriginDependencyAudit

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
-- Inspect every new checked declaration, including the inherited coefficient topology.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.ValuationInertia.mem_decomposition_of_mem_inertia #[]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationInertia.decomposition_conj_mem_inertia #[]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationInertia.decomposition_inv_conj_mem_inertia #[``DkMath.Lib.NumberTheory.ValuationInertia.decomposition_conj_mem_inertia]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCoefficient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCoefficientTopology #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle_apply #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_orbit_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalClass_zero #[``groupCohomology.H1π_eq_zero_iff]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalInertiaCoefficient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalInertiaRestriction #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_restrict #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalClass_restrict #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_restrict, ``groupCohomology.H1π_comp_map_apply]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_restriction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_include_value, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_eq]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_preserves_fixed #[``DkMath.Lib.NumberTheory.ValuationInertia.decomposition_inv_conj_mem_inertia]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_preserves_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionCoefficient #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction_injective #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalTranslateTorsion #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalTranslate_upperClass #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_conjugate #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_decomposition_conjugate #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_conjugate, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_restriction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_origin #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousClass_global_origin_square #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_origin, ``groupCohomology.H1π_comp_map_apply]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.relative_global_class_boundary #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalClass_zero, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_continuous_nonzero #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_decomposition_conjugate, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction_injective, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_nontrivial]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_class_boundary #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_continuous_nonzero, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalClass_zero]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationInertia.mem_decomposition_of_mem_inertia #[`A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationInertia.decomposition_conj_mem_inertia #[`A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationInertia.decomposition_inv_conj_mem_inertia #[`A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCoefficient #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCoefficientTopology #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle_apply #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle_continuous #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalClass_zero #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalInertiaCoefficient #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalInertiaRestriction #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_restrict #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalClass_restrict #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_restriction #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_preserves_fixed #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionCoefficient #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction_injective #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalTranslateTorsion #[`σ, `x] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalTranslate_upperClass #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_conjugate #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_decomposition_conjugate #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_origin #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousClass_global_origin_square #[`T] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.relative_global_class_boundary #[`h, `hp5] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_continuous_nonzero #[`h, `hp5] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_class_boundary #[`h, `hp5] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `hstable, `horigin, `hvanish, `hreflect, `hherbrand]

end Note032RelativeOriginDependencyAudit
