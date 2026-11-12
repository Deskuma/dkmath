/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia

/-!
# 符号から分離した悪い素点の吸収を、実際の証明依存で監査する

Frobenius の剰余作用、単元次数の根の剛性、臨界中心の恒等式、深さと二枝、
巡回群の符号分離、滑らかな捩れの還元上界と固定性への到達を要求する。
これらを二択・濃度・吸収 provider へ移した証明を許容しない。
-/

namespace Note032NonresonantInertiaDependencyAudit

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
-- Finite traversal includes imported types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.cyclotomicCharacter_eq_natCast
    #[``DkMath.Lib.NumberTheory.CyclotomicFrobenius.apply_root_eq_pow,
      ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.roots_eq_of_congruent,
      ``DkMath.Lib.NumberTheory.ValuationInertiaPower.valuation_sub_one_eq_one,
      ``DkMath.Lib.NumberTheory.ValuationFrobenius.IsFrobeniusAt.smul_residue_eq]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalDecomposition.centre_decomposition_fixed
    #[``DkMath.Lib.NumberTheory.EllipticNodalDecomposition.defect_identity,
      ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.valuation_apply_eq]
  checkRoot ``DkMath.FLT.Frey.Source.cyclic_tower_eq_smooth_torsion_of_nonresonant
    #[``DkMath.Lib.NumberTheory.CyclotomicFrobenius.cyclotomicCharacter_eq_natCast,
      ``DkMath.Lib.Algebra.CyclicSignSeparation.le_of_sub_or_add_mem,
      ``DkMath.Lib.NumberTheory.EllipticNodalDecomposition.sub_or_add_smooth_of_odd_torsion,
      ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth_of_model,
      ``DkMath.Lib.NumberTheory.EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion]
  checkRoot ``DkMath.FLT.Frey.Source.preimage_pointAction_sub_mem_of_nonresonant_bad
    #[``DkMath.FLT.Frey.Source.cyclic_tower_eq_smooth_torsion_of_nonresonant,
      ``DkMath.FLT.Frey.Source.inertia_difference_smooth_at_bad_address,
      ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction]
  checkRoot ``DkMath.FLT.Frey.Source.residual_preimage_unramified_away_of_resonant_inertia
    #[``DkMath.FLT.Frey.Source.preimage_pointAction_sub_mem_of_nonresonant_bad,
      ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.fixed_of_inertia_of_good_model]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_tower_resonant_inertia_frobenius_impossible
    #[``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_nonresonant_bad,
      ``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_cyclic_tower_at_p,
      ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
      ``DkMath.Lib.Algebra.TorsionTowerFrobenius.nsmul_mem_of_frobenius_relation]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.cyclotomicCharacter_eq_natCast
    #[`hq, `hqp, `hA, `hσ] #[`hchar, `hroot, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalDecomposition.sub_or_add_smooth_of_odd_torsion
    #[`hmodel, `C, `D, `hodd, `hn, `hunit, `hσ, `ht, `hout]
    #[`hfix, `hlev, `hsh, `hDich, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.cyclic_tower_eq_smooth_torsion_of_nonresonant
    #[`hp5, `hline, `hcofixed, `K, `hstable, `hm, `hcard, `hbase, `hqp, `hq1, `hqneg, `hA]
    #[`C, `D, `hDich, `hMcard, `hFcard, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.preimage_pointAction_sub_mem_of_nonresonant_bad
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hqp, `hq1, `hqneg, `hA, `hτ, `hy]
    #[`habs, `hfixed, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_preimage_unramified_away_of_resonant_inertia
    #[`hp5, `hcofixed, `hstable, `hm, `hcard, `hbase, `hbad, `hqp, `hA, `hτ]
    #[`hunram, `habs, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_tower_resonant_inertia_frobenius_impossible
    #[`hp5, `hcofixed, `hstable, `hN, `hcard, `hbase, `hbad, `hCH]
    #[`hdown, `hfixed, `hpabs, `hSp, `hcompl, `hEXT, `hno]

end Note032NonresonantInertiaDependencyAudit
