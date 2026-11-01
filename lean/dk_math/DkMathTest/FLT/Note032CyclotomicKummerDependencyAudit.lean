/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummer

/-!
# 同じ指標核・同じ体・同じ Kummer 根の依存監査

逆 Kummer 構成、既約性、次数の内部供給、元の核の検出、
同じ付値環での局所固定性を実際の証明依存として要求する。
-/

namespace Note032CyclotomicKummerDependencyAudit

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
-- Seven finite traversals inspect imported types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclicKummer.exists_presentation
    #[``exists_root_adjoin_eq_top_of_isCyclic,
      ``irreducible_X_pow_sub_C_of_root_adjoin_eq_top,
      ``Module.End.hasEigenvalue_of_isRoot]
  checkRoot ``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.autEquivRoots_ratio
    #[``autEquivRootsOfUnity_smul,
      ``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.radical_ne_zero,
      ``isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicCharacterKummer.exists_presentation
    #[``DkMath.Lib.NumberTheory.CyclicKummer.exists_presentation,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_finrank,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_isGalois,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.relative_isCyclic,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterKummer.rootField_primitiveRoots]
  checkRoot ``DkMath.FLT.Frey.Source.residual_nonsplit_has_kummer_presentation
    #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_has_surjective_character,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterKummer.exists_presentation]
  checkRoot ``DkMath.FLT.Frey.Source.residual_character_eq_one_iff_fix_kummer_radical
    #[``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.algHom_ext,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.fixingSubgroup_characterField,
      ``IntermediateField.mem_fixedField_iff,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_radical_decomposition_fixed_at_p
    #[``DkMath.FLT.Frey.Source.residual_characterField_decomposition_fixed_at_p,
      ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_locally_split_at_p,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_decomposition_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_radical_inertia_fixed_away
    #[``DkMath.FLT.Frey.Source.residual_characterField_inertia_fixed_away,
      ``DkMath.FLT.Frey.Source.residual_preimage_unramified_away_of_resonant_inertia,
      ``DkMath.FLT.Frey.Source.preimage_pointAction_sub_mem_of_nonresonant_bad]
  checkInputs ``DkMath.Lib.NumberTheory.CyclicKummer.exists_presentation
    #[`hdegree, `hroots] #[`hroot, `hgen, `hpoly, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.autEquivRoots_smul
    #[`P, `hdegree, `hroots, `σ] #[`haction, `hpairing, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicCharacterKummer.exists_presentation
    #[`ψ, `hζ, `hopen, `hsurj, `hC, `hweight] #[`hroot, `hgen, `hpoly, `hdegree, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_nonsplit_has_kummer_presentation
    #[`hp5, `hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hns]
    #[`hroot, `hgen, `hpoly, `hfield, `hfinite, `hGalois, `hdegree, `hweight, `hopen, `hsurj,
      `hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_character_eq_one_iff_fix_kummer_radical
    #[`P, `v, `hζ, `g] #[`hkernel, `hfix, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_radical_decomposition_fixed_at_p
    #[`P, `v, `hp5, `hζ, `hA, `hg] #[`hSp, `hcompl, `hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_radical_inertia_fixed_away
    #[`P, `v, `hp5, `hζ, `hbad, `hqp, `hA, `hg] #[`hunram, `hzero, `hEXT, `hno]

end Note032CyclotomicKummerDependencyAudit
