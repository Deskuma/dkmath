/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTailKernelVanishing

#print "file: DkMathTest.FLT.Note032InertiaTailDependencyAudit"

namespace Note032InertiaTailDependencyAudit

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
-- Traverse all new checked proofs, their types and constructors without an axiom shortcut.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.fixedField_topologicalClosure_eq #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.fixingSubgroup_fixedField_eq_topologicalClosure #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.exists_mem_apply_eq_of_mem_fixingSubgroup #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.isOpen_setOf_apply #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.isClosed_setOf_apply #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.mem_inertia_map_iff #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.isClosed_inertia_map #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.topologicalClosure_inertia_map #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaClosed.fixingSubgroup_fixedField_inertia #[``DkMath.Lib.NumberTheory.InertiaClosed.topologicalClosure_inertia_map, ``DkMath.Lib.NumberTheory.InertiaClosed.fixingSubgroup_fixedField_eq_topologicalClosure]
  checkRoot ``DkMath.Lib.NumberTheory.KummerPrimeQuotient.index_coprime_of_forall_pow_surjective #[``exists_root_adjoin_eq_top_of_isCyclic, ``exists_prime_orderOf_dvd_card]
  checkRoot ``DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.eq_one_of_forall_mem_openNormalSubgroup #[]
  checkRoot ``DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.exists_pow_mul_inv_mem #[]
  checkRoot ``DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.exists_pow_pow_eq #[``DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.exists_pow_mul_inv_mem, ``DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.eq_one_of_forall_mem_openNormalSubgroup, ``IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailIntermediate_exact_pRoot #[``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_exact_pRoot]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_primitiveRoot #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailGalois_index_coprime #[``DkMath.Lib.NumberTheory.InertiaResidue.tailIntermediate_exact_pRoot, ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_primitiveRoot, ``DkMath.Lib.NumberTheory.KummerPrimeQuotient.index_coprime_of_forall_pow_surjective]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailFixing_inertia_pRoot #[``DkMath.Lib.NumberTheory.InertiaResidue.tailGalois_index_coprime, ``DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.exists_pow_pow_eq, ``DkMath.Lib.NumberTheory.InertiaClosed.fixingSubgroup_fixedField_inertia]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.mem_tailFixing_iff_all_radicals #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_inertia_pRoot #[``DkMath.Lib.NumberTheory.InertiaResidue.tailFixing_inertia_pRoot, ``DkMath.Lib.NumberTheory.InertiaResidue.mem_tailFixing_iff_all_radicals]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_map_eq_one #[``DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_inertia_pRoot]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one #[``DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_map_eq_one, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_stage]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_evaluations_eq_zero #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_fixed_differences_eq_one #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tailFixing_le_commonProjection_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailIntermediate_exact_pRoot #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_primitiveRoot #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailGalois_index_coprime #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailFixing_inertia_pRoot #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.mem_tailFixing_iff_all_radicals #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_inertia_pRoot #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_map_eq_one #[`A] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_evaluations_eq_zero #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_fixed_differences_eq_one #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tailFixing_le_commonProjection_kernel #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous]

end Note032InertiaTailDependencyAudit
