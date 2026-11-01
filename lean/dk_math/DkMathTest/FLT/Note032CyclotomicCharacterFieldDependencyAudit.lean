/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicCharacterField

/-!
# 実際の円分体と巡回 p 拡大の依存監査

元の指標の核、開性、無限 Galois 対応、次数の塔、元の非分裂終点、
同じ付値環での分解群・慣性と局所分裂への到達を要求する。
類群・単数による消滅を仮定に移していないことを確認する。
-/

namespace Note032CyclotomicCharacterFieldDependencyAudit

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
-- Seven finite traversals include imported types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKernelField.fixingSubgroup_eq_kernel
    #[``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec,
      ``IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_inertia_iff
    #[``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_of_forall,
      ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_sub_self_mem_nonunits]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.fixingSubgroup_characterField
    #[``InfiniteGalois.fixingSubgroup_fixedField,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernel_isOpen,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.kernelInGalois_isOpen]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_finrank
    #[``IntermediateField.finrank_eq_fixingSubgroup_index,
      ``Module.finrank_mul_finrank,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.rootField_finrank,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.characterField_finrank]
  checkRoot ``DkMath.FLT.Frey.Source.residual_nonsplit_has_cyclotomic_cyclic_extension
    #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_has_surjective_character,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_isCyclic,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_isGalois,
      ``InfiniteGalois.normal_iff_isGalois]
  checkRoot ``DkMath.FLT.Frey.Source.residual_characterField_decomposition_fixed_at_p
    #[``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_decomposition_iff,
      ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_locally_split_at_p,
      ``IntermediateField.mem_fixedField_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residual_characterField_inertia_fixed_away
    #[``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_inertia_iff,
      ``DkMath.FLT.Frey.Source.residual_preimage_unramified_away_of_resonant_inertia,
      ``DkMath.FLT.Frey.Source.preimage_pointAction_sub_mem_of_nonresonant_bad,
      ``IntermediateField.mem_fixedField_iff]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKernelField.fixingSubgroup_eq_kernel
    #[`hζ] #[`hker, `hfix, `hEXT, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_inertia_iff
    #[`hζ, `A, `g] #[`hI, `htransport, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.fixingSubgroup_characterField
    #[`ψ, `hopen] #[`hclosed, `hfixedField, `hEXT, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_finrank
    #[`ψ, `hζ, `hopen, `hsurj] #[`hdegree, `hfinite, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_nonsplit_has_cyclotomic_cyclic_extension
    #[`hp5, `hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hns]
    #[`hfield, `hfinite, `hGalois, `hdegree, `hweight, `hopen, `hsurj, `hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_characterField_decomposition_fixed_at_p
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hA, `hg]
    #[`hSp, `hcompl, `hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_characterField_inertia_fixed_away
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hbad, `hqp, `hA, `hg]
    #[`hunram, `hzero, `hEXT, `hno]

end Note032CyclotomicCharacterFieldDependencyAudit
