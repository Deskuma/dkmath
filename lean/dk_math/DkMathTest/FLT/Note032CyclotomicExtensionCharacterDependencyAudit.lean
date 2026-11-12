/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicExtensionCharacter

/-!
# 円分指標核上の実際の障害と、局所消滅・次段の依存監査

類群・単数の消滅は未実装。実際の指標、逆指標の共役、開核、局所分裂、
条件付きの塔の次段に到達することと、未実装の仮定が公開型に残ることを確認する。
-/

namespace Note032CyclotomicExtensionCharacterDependencyAudit

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
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate
    #[``DkMath.Lib.RepresentationTheory.FixedLineExtension.deviation_conjugate,
      ``DkMath.Lib.RepresentationTheory.FixedLineExtension.deviationAt,
      ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_quotient_cyclotomic,
      ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_profile]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_at_p
    #[``DkMath.Lib.RepresentationTheory.FixedLineExtension.eq_one_of_complement,
      ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_locally_split_at_p,
      ``DkMath.FLT.Frey.Source.primePowerReductionFiltration_cyclic_and_card,
      ``DkMath.Lib.NumberTheory.CyclotomicInertia.exists_inertia_cyclotomic_eq]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen
    #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.preimageRepresentation_kernel_isOpen,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen_of_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_inertia_away
    #[``DkMath.FLT.Frey.Source.preimage_pointAction_sub_mem_of_nonresonant_bad,
      ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.fixed_of_inertia_of_good_model]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_splits_iff_character_trivial
    #[``DkMath.Lib.RepresentationTheory.FixedLineExtension.isCompl_eigenKernel,
      ``DkMath.Lib.RepresentationTheory.FixedLineExtension.kernel_trivial_iff_deviationAt_trivial,
      ``DkMath.Lib.NumberTheory.CyclotomicInertia.exists_inertia_cyclotomic_eq]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_has_surjective_character
    #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_splits_iff_character_trivial,
      ``Subgroup.card_subgroup_dvd_card,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsionImage_of_cyclic]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_tower_step_of_character_trivial
    #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_splits_iff_character_trivial,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_tower_step_of_stable_complement,
      ``DkMath.Lib.Algebra.PrimePowerCyclicCriterion.isAddCyclic_and_card_dvd_of_prime_power_exponent]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `σ, `g]
    #[`hweight, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_at_p
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hA, `hg]
    #[`hSp, `hcompl, `hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen
    #[`hcofixed, `hstable, `hm, `hcard, `hbase, `v]
    #[`hopen, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_inertia_away
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hbad, `hqp, `hA, `hg]
    #[`hunram, `hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_splits_iff_character_trivial
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase]
    #[`hzero, `hcompl, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_has_surjective_character
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hns]
    #[`hzero, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_tower_step_of_character_trivial
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hzero]
    #[`hcompl, `hEXT, `hno]

end Note032CyclotomicExtensionCharacterDependencyAudit
