/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedTorsionExtension
import DkMath.FLT.FreyTorsionInertiaAbsorption

/-!
# 捩れ extension の実依存と公開入力の回帰監査

型と opaque 本体を走査し、既存の絶対慣性生成・幾何学的有限性・倍写像の全射性へ
実際に到達することを確認する。完成済み FLT や外部終点への依存で置換していない。
局所吸収・安定な補部分加群・Frobenius 関係式という残る入力は、型に明示して残す。
-/

namespace Note032TorsionExtensionDependencyAudit

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
-- This command traverses a finite dependency graph, including opaque bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_sub_mem_of_inertia_absorbs
    #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isCofixedOn_of_inertia,
      ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residual_line_tower_inertia_frobenius_impossible
    #[``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_bad_inertia,
      ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.fixed_of_inertia_of_good_model,
      ``DkMath.Lib.Algebra.TorsionTowerFrobenius.nsmul_mem_of_frobenius_relation,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_preimage_extension_profile
    #[``DkMath.Lib.Algebra.TorsionPreimageQuotient.card_quotient,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.preimageRepresentation_kernel_isOpen,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.preimageRepresentation_fixed_torsionImage_of_cofixed]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_preimage_quotient_cyclotomic
    #[``DkMath.FLT.Frey.Source.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.representation_sub_nsmul_mem_torsionImage]
  checkRoot ``DkMath.FLT.Frey.Source.residual_preimage_stable_complement_lifts
    #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_tower_step_of_stable_complement,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.card_liftSubmodule,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.torsion_mem_of_lift_disjoint,
      ``DkMath.Lib.Algebra.PrimePowerCyclicCriterion.isAddCyclic_and_card_dvd_of_prime_power_exponent]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_sub_mem_of_inertia_absorbs
    #[`E, `hn, `K, `hlocal] #[`hgen, `hopen, `hglobal, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_line_tower_inertia_frobenius_impossible
    #[`S, `L, `hline, `K, `hN, `hdown, `hbad, `σ, `ell, `hCH]
    #[`hfixed, `hglobal, `hgen, `hopen, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_preimage_extension_profile
    #[`S, `L, `hline, `hcofixed] #[`hcard, `hopen, `hcompl, `hCstable, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_preimage_stable_complement_lifts
    #[`S, `L, `hline, `hcofixed, `C', `hcompl, `hstable] #[`hno, `hEXT]

end Note032TorsionExtensionDependencyAudit
