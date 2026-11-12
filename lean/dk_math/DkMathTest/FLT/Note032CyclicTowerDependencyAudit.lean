/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedTorsionTower

#print "file: DkMathTest.FLT.Note032CyclicTowerDependencyAudit"

/-!
# 全段の円分商・局所補直線・最終矛盾の実依存

型と opaque 本体を辿り、実際の巡回群の倍写像と楕円曲線の幾何へ到達することを要求する。
安定な補直線や大域 extension 消滅の provider を仮定した完成宣言は認めない。
-/

namespace Note032CyclicTowerDependencyAudit

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
-- The full traversal is finite, including imported opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.TorsionPreimageQuotient.torsionImageQuotientEquiv
    #[``DkMath.Lib.Algebra.TorsionPreimageQuotient.quotientMultiplyMod_surjective,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.mem_torsionImage_iff_quotientMultiplyMod_eq_zero,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.multiply_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_quotient_cyclotomic
    #[``DkMath.FLT.Frey.Source.residual_cyclic_tower_socle_mem_base,
      ``DkMath.FLT.Frey.Source.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul,
      ``DkMath.Lib.Algebra.CyclicPrimePowerScalar.sub_nsmul_mem_range_of_socle,
      ``DkMath.Lib.Algebra.CyclicPrimePowerScalar.range_nsmul_eq_ker]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_profile
    #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.preimageRepresentation_kernel_isOpen,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.preimageRepresentation_fixed_torsionImage_of_cofixed,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_complement_of_local_subgroup
    #[``DkMath.Lib.Algebra.TorsionPreimageQuotient.isCompl_imageSubmodule,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.imageSubmodule_stable,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.lift_imageSubmodule,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq]
  checkRoot ``DkMath.FLT.Frey.Source.residual_preimage_unramified_away_of_bad_inertia
    #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_eq_of_inertia_of_integer_good,
      ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.fixed_of_inertia_of_good_model,
      ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_dvd_integral_discriminant_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_tower_inertia_frobenius_impossible
    #[``DkMath.Lib.Algebra.CyclicPrimePowerScalar.socle_mem_of_prime_subgroup,
      ``DkMath.FLT.Frey.Source.residual_line_tower_inertia_frobenius_impossible,
      ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
      ``DkMath.Lib.Algebra.TorsionTowerFrobenius.nsmul_mem_of_frobenius_relation]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_quotient_cyclotomic
    #[`hcofixed, `hstable, `hm, `hcard, `hbase]
    #[`hKkill, `hsocle, `hCyc, `hcompl, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_profile
    #[`hcofixed, `hstable, `hm, `hcard, `hbase]
    #[`hKtors, `hopen, `hfixed, `hcompl, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_complement_of_local_subgroup
    #[`hstable, `hKF, `hFP, `hFcard, `hFdown, `hFstable]
    #[`hcompl, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_preimage_unramified_away_of_bad_inertia
    #[`hstable, `hcard, `hbad, `hq, `hqp, `hA, `hτ]
    #[`hunram, `hfixed, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_tower_inertia_frobenius_impossible
    #[`hm, `hcard, `hbase, `hbad, `hCH]
    #[`hdown, `hfixed, `hglobal, `hgen, `hopen, `hEXT, `hno]

end Note032CyclicTowerDependencyAudit
