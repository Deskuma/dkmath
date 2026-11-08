/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameCyclicClosure

#print "file: DkMathTest.FLT.Note032FiniteKernelDependencyAudit"

namespace Note032FiniteKernelDependencyAudit

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
-- Audit all checked new proofs, their types and constructors recursively.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_eq_preimage #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_isOpen #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_kernel_isOpen, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_eq_preimage, ``QuotientGroup.continuous_mk]
  checkRoot ``DkMath.Lib.NumberTheory.CompactKernel.exists_subset_open #[``IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.inertia_compactSpace #[``DkMath.Lib.NumberTheory.InertiaClosed.isClosed_inertia_map]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character_kernel_antitone #[``DkMath.Lib.NumberTheory.InertiaRadical.character_compat]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character_kernel_isClosed #[``DkMath.Lib.NumberTheory.InertiaClosed.isClosed_setOf_apply, ``DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.all_radicals_fixed_of_tower #[``DkMath.Lib.NumberTheory.InertiaRadical.inertia_fixes_primePower_root]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.forall_character_kernel_iff_all_radicals #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.iInter_character_kernel_eq_tail #[``DkMath.Lib.NumberTheory.InertiaRadical.forall_character_kernel_iff_all_radicals, ``DkMath.Lib.NumberTheory.InertiaResidue.mem_tailFixing_iff_all_radicals]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_radical_kernel_le_common #[``DkMath.Lib.NumberTheory.CompactKernel.exists_subset_open, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_isOpen, ``DkMath.Lib.NumberTheory.InertiaRadical.forall_character_kernel_iff_all_radicals]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_le_commonProjection_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_radical_kernel_le_common, ``DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_stage]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_fixed_evaluations_eq_zero #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_le_commonProjection_kernel, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_evaluations]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generator_generates #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_le_commonProjection_kernel, ``DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonTame_isCyclic #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generator_generates]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generator_generates, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_card_dvd_fixed_of_radical_generator #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_eq_preimage #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_isOpen #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.inertia_compactSpace #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character_kernel_antitone #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character_kernel_isClosed #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.all_radicals_fixed_of_tower #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.forall_character_kernel_iff_all_radicals #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.iInter_character_kernel_eq_tail #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_radical_kernel_le_common #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_le_commonProjection_kernel #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_fixed_evaluations_eq_zero #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generator_generates #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonTame_isCyclic #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_card_dvd_fixed_of_radical_generator #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive]

end Note032FiniteKernelDependencyAudit
