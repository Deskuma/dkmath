/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalExactRoots

#print "file: DkMathTest.NumberTheory.Note032ExactRadicalDependencyAudit"

namespace Note032ExactRadicalDependencyAudit

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
-- Check every new theorem recursively, including types, opaque proofs and constructors.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.InertiaStability.isClosed_apply_mem #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaStability.isClosed_decompositionSubgroup #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaStability.fixingSubgroup_fixedField_map_inertia_le #[``DkMath.Lib.NumberTheory.InertiaStability.isClosed_decompositionSubgroup, ``InfiniteGalois.fixingSubgroup_fixedField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaStability.smul_eq_self_of_mem_fixingSubgroup #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaStability.overfield_stable #[``DkMath.Lib.NumberTheory.InertiaStability.smul_eq_self_of_mem_fixingSubgroup]
  checkRoot ``DkMath.Lib.NumberTheory.StableValuation.isUnit_iff_inv_mem #[]
  checkRoot ``DkMath.Lib.NumberTheory.StableValuation.mem_maximalIdeal_iff #[]
  checkRoot ``DkMath.Lib.NumberTheory.StableValuation.mem_maximalIdeal_iff_map #[]
  checkRoot ``DkMath.Lib.NumberTheory.StableValuation.hensel_of_stable #[``InfiniteGalois.fixedField_bot]
  checkRoot ``DkMath.Lib.NumberTheory.StableValuation.henselianLocalRing_comap #[]
  checkRoot ``DkMath.Lib.NumberTheory.StableValuation.overfield_henselian #[``DkMath.Lib.NumberTheory.StableValuation.henselianLocalRing_comap, ``DkMath.Lib.NumberTheory.InertiaStability.overfield_stable]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.exists_pow_eq_of_pow_sub_mem #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.prime_isUnit_comap #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.exact_unit_pRoot #[``DkMath.Lib.NumberTheory.StableValuation.overfield_henselian, ``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot, ``DkMath.Lib.NumberTheory.InertiaResidue.prime_isUnit_comap, ``DkMath.Lib.NumberTheory.InertiaResidue.exists_pow_eq_of_pow_sub_mem]
  checkRoot ``DkMath.Lib.NumberTheory.RationalValue.valuation_natCast_eq_one #[]
  checkRoot ``DkMath.Lib.NumberTheory.RationalValue.valuation_intCast #[]
  checkRoot ``DkMath.Lib.NumberTheory.RationalValue.valuation_ratCast #[]
  checkRoot ``DkMath.Lib.NumberTheory.RationalValue.exists_valuation_pow_eq #[]
  checkRoot ``DkMath.Lib.NumberTheory.RadicalValue.eq_one_of_pow_eq_one #[]
  checkRoot ``DkMath.Lib.NumberTheory.RadicalValue.exists_valuation_eq_pow #[``DkMath.Lib.NumberTheory.RadicalValue.eq_one_of_pow_eq_one]
  checkRoot ``DkMath.Lib.NumberTheory.RadicalDescent.exists_pow_eq #[``DkMath.Lib.NumberTheory.RationalValue.exists_valuation_pow_eq, ``DkMath.Lib.NumberTheory.RadicalValue.exists_valuation_eq_pow, ``DkMath.Lib.NumberTheory.InertiaResidue.exists_pow_eq_of_pow_sub_mem]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_exact_pRoot #[``DkMath.Lib.NumberTheory.RadicalDescent.exists_pow_eq, ``DkMath.Lib.NumberTheory.InertiaStability.overfield_stable, ``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot, ``DkMath.Lib.NumberTheory.InertiaResidue.tower_mem_tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_exact_pRoot #[``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_exact_pRoot]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_power_surjective #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_primePower_surjective #[``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_power_surjective]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaStability.overfield_stable #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.StableValuation.overfield_henselian #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.prime_isUnit_comap #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.exact_unit_pRoot #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_exact_pRoot #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_exact_pRoot #[`A, `a, `ha] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_power_surjective #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_primePower_surjective #[`A, `E] #[`hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen]

end Note032ExactRadicalDependencyAudit
