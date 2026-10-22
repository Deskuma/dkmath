/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.InertiaLocalGlobal
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031FiniteInertiaDependencyAudit"

/-!
# NOTE-031-001A: 有限段階の慣性生成・Fixed/Cofixed輸送の監査

全新規公開宣言の公理を検査し、主要経路では型とopaque本体まで走査する。
分岐指数の塔と慣性群の位数、Minkowskiの帰結、有限ガロア対応への到達を要求する。
有限数体の輸送は生成性を外部入力に取らない。純群論と二択の境界例は数体の算術を使わない。
ZModの一般加群インスタンスは環のイデアルを使うため、Ideal全体ではなく分岐・慣性APIを排除する。
Frey・旧FLT・外部provider・Kummer・整数折り返し核への依存は禁止する。
絶対ガロア群の慣性持ち上げとFrey局所算術を完了したとはしない。
-/
namespace Note031FiniteInertiaDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "DkMath.FLT." ||
    s.startsWith "DkMath.Lib.NumberTheory.RegularKummer." ||
    s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit." || s.startsWith "FltRegular." || s.startsWith "P2M." ||
    s.startsWith "P2MW." || s.startsWith "FreyPackage." ||
    s.contains "fermatLastTheorem" || s.contains "fermat_last_theorem" ||
    s.contains "fermatThree_no_positive_solution" ||
    (`DkMath.FLT.Kummer).isPrefixOf (privateToUserName n)

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false)
    (algebraOnly : Bool := false) (withoutFolded : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let s := (privateToUserName n).toString
    if forbidden n || (neutral && s.startsWith "DkMath.FLT.") ||
        (withoutFolded && s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit.") ||
        (algebraOnly && (s.startsWith "NumberField." || s.startsWith "Ideal.inertia" ||
          s.startsWith "Ideal.ramification" ||
          s.startsWith "DkMath.Lib.NumberTheory." ||
          s.startsWith "WeierstrassCurve.")) then
      throwError "Forbidden dependency: {n}"
    let some info := env.checked.get.find? n | throwError "Missing constant: {n}"
    pending := pending ++ info.type.getUsedConstants
    if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    match info.value? (allowOpaque := true) with
    | some value => pending := pending ++ value.getUsedConstants
    | none =>
      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => throwError "Unreadable body: {n}"
      | _ => pure ()
  for n in required do
    unless visited.contains n do throwError "Required provider absent: {n}"
  logInfo m!"PASS: {root}; {visited.size} reachable constants; expected providers present."

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input missing in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; explicit arithmetic guards and remaining inputs retained."

set_option maxHeartbeats 0 in
-- 型とopaque本体を含む有限の依存グラフを走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_unramifiedAt_int_of_inertia_le,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_finrank_eq_one_of_inertia_le,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.iSup_inertia_eq_top,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.FixedOn,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.CofixedOn,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.fixedSubgroup,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.cofixedSubgroup,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.fixedOn_iff_le,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.cofixedOn_iff_le,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.isFixedOn_of_iSup_eq_top,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.isCofixedOn_of_iSup_eq_top,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.fixed_or_cofixed_of_common_side,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isFixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isCofixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.fixed_or_cofixed_of_inertia_common_side]
  let regression : Array Name := #[``InertiaLocalGlobalTest.RootField,
    ``InertiaLocalGlobalTest.rootField_degree,
    ``InertiaLocalGlobalTest.rootField_inertia_generates,
    ``InertiaLocalGlobalTest.rootField_has_nontrivial_inertia,
    ``InertiaLocalGlobalTest.rootField_fixed_transport,
    ``InertiaLocalGlobalTest.rootField_cofixed_transport,
    ``InertiaLocalGlobalTest.SideBoundary.k,
    ``InertiaLocalGlobalTest.SideBoundary.G,
    ``InertiaLocalGlobalTest.SideBoundary.V,
    ``InertiaLocalGlobalTest.SideBoundary.action,
    ``InertiaLocalGlobalTest.SideBoundary.rho,
    ``InertiaLocalGlobalTest.SideBoundary.line,
    ``InertiaLocalGlobalTest.SideBoundary.line_eq_span,
    ``InertiaLocalGlobalTest.SideBoundary.line_finrank,
    ``InertiaLocalGlobalTest.SideBoundary.line_stable,
    ``InertiaLocalGlobalTest.SideBoundary.first,
    ``InertiaLocalGlobalTest.SideBoundary.second,
    ``InertiaLocalGlobalTest.SideBoundary.localGroups,
    ``InertiaLocalGlobalTest.SideBoundary.localGroups_generate,
    ``InertiaLocalGlobalTest.SideBoundary.first_cofixed,
    ``InertiaLocalGlobalTest.SideBoundary.second_fixed,
    ``InertiaLocalGlobalTest.SideBoundary.pointwise_local_alternative,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_fixed,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_cofixed,
    ``InertiaLocalGlobalTest.SideBoundary.inconsistent_side_counterexample]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_unramifiedAt_int_of_inertia_le #[``Ideal.card_inertia_eq_ramificationIdxIn,
    ``Ideal.ramificationIdx'_algebra_tower',
    ``Ideal.ramificationIdx_eq_one_iff] true false false
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_finrank_eq_one_of_inertia_le #[``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_unramifiedAt_int_of_inertia_le,
    ``NumberField.exists_not_isUnramifiedAt_int,
    ``NumberField.abs_discr_gt_two] true false false
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le #[``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_finrank_eq_one_of_inertia_le,
    ``IsGaloisGroup.card_eq_finrank] true false false
  checkRoot ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.isFixedOn_of_iSup_eq_top #[``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.fixedSubgroup] true true false
  checkRoot ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.isCofixedOn_of_iSup_eq_top #[``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.cofixedSubgroup] true true false
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isFixedOn_of_inertia #[``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.iSup_inertia_eq_top,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.isFixedOn_of_iSup_eq_top,
    ``NumberField.exists_not_isUnramifiedAt_int] true false false
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isCofixedOn_of_inertia #[``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.iSup_inertia_eq_top,
    ``DkMath.Lib.RepresentationTheory.LocalFixedCofixed.isCofixedOn_of_iSup_eq_top,
    ``NumberField.exists_not_isUnramifiedAt_int] true false false
  checkRoot ``InertiaLocalGlobalTest.rootField_has_nontrivial_inertia #[``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``InertiaLocalGlobalTest.rootField_degree] true false false
  checkRoot ``InertiaLocalGlobalTest.SideBoundary.inconsistent_side_counterexample #[``InertiaLocalGlobalTest.SideBoundary.localGroups_generate,
    ``InertiaLocalGlobalTest.SideBoundary.line_finrank,
    ``InertiaLocalGlobalTest.SideBoundary.line_stable,
    ``InertiaLocalGlobalTest.SideBoundary.pointwise_local_alternative,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_fixed,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_cofixed] true true false
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.iSup_inertia_eq_top #[]
    #[`hH, `hgen, `hglobal]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isFixedOn_of_inertia #[`ρ, `N, `hlocal]
    #[`hgen, `hglobal, `hH]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isCofixedOn_of_inertia #[`ρ, `N, `hlocal]
    #[`hgen, `hglobal, `hH]

#print axioms DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le
#print axioms DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isFixedOn_of_inertia
#print axioms InertiaLocalGlobalTest.SideBoundary.inconsistent_side_counterexample

end Note031FiniteInertiaDependencyAudit
