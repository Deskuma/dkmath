/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyStableLineLocalGlobal
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031StableLineLocalGlobalDependencyAudit"

/-!
# NOTE-031-005: 三つの局所経路、大域化、hcases供給の依存監査

型とopaque本体を走査し、2,p,その他の局所算術と実際の慣性生成・大域化への到達を要求する。
局所・大域二択にはFoldedValuationOrbitへの依存を禁止する。
Cofixed選択にはNOTE-030の有理torsion排除と実装済みの整数付値軌道を使うため、その経路を要求する。
全宣言は標準論理公理のみを許し、外部FLT終点・P2M・RegularKummerなどは全経路で禁止する。
公開型からhcasesを除き、既約性の条件付き入口にhnoが残ることを検査する。
-/
namespace Note031StableLineLocalGlobalDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "DkMath.Lib.NumberTheory.RegularKummer." || s.startsWith "FltRegular." || s.startsWith "P2M." ||
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
        (algebraOnly && (s.startsWith "DkMath.Lib.NumberTheory.Elliptic" ||
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
-- 型とopaque本体を含む有限依存グラフの全走査に限って上限を外す。
run_cmd do
  let production : Array Name := #[``DkMath.FLT.Frey.Source.residual_inertia_common_side_of_stable,
    ``DkMath.FLT.Frey.Source.residual_stable_submodule_fixed_or_cofixed,
    ``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed,
    ``DkMath.FLT.Frey.Source.residual_stable_line_cofixed_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible,
    ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_cofixed_obstruction,
    ``DkMath.FLT.Frey.Source.residual_not_irreducible_iff_exists_cofixed_line_of_oriented,
    ``DkMath.FLT.Frey.Source.ofCounterexample_residual_exists_cofixed_line]
  let regression : Array Name := #[``FreyStableLineLocalGlobalTest.source37_dichotomy,
    ``FreyStableLineLocalGlobalTest.source37_stable_line_cofixed,
    ``FreyStableLineLocalGlobalTest.source37_cofixed_of_reducible,
    ``FreyStableLineLocalGlobalTest.source37_irreducible_with_obstruction,
    ``FreyStableLineLocalGlobalTest.counterexample37_profile,
    ``FreyStableLineLocalGlobalTest.actual_two_boundary,
    ``FreyStableLineLocalGlobalTest.incompatible_local_sides_boundary]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.FLT.Frey.Source.residual_inertia_common_side_of_stable #[``DkMath.FLT.Frey.Source.residual_common_side_at_p,
    ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two,
    ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self] false false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_stable_submodule_fixed_or_cofixed #[``DkMath.FLT.Frey.Source.residual_inertia_common_side_of_stable,
    ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_of_inertia_common_side,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``NumberField.abs_discr_gt_two] false false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed #[``DkMath.FLT.Frey.Source.residual_stable_submodule_fixed_or_cofixed,
    ``DkMath.Lib.RepresentationTheory.proper_nonzero_iff_finrank_one] false false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_stable_line_cofixed_of_oriented #[``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed,
    ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible #[``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_cofixed_obstruction #[``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_no_cofixed_line,
    ``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_not_irreducible_iff_exists_cofixed_line_of_oriented #[``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_iff_no_stable_line] false false false
  checkRoot ``DkMath.FLT.Frey.Source.ofCounterexample_residual_exists_cofixed_line #[``DkMath.FLT.Frey.Source.ofCounterexample,
    ``DkMath.FLT.Frey.Source.ofCounterexample_spec,
    ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible,
    ``DkMath.FLT.Frey.PrimitiveReduction,
    ``DkMath.FLT.Frey.OrientationTrace] false false false
  checkRoot ``FreyStableLineLocalGlobalTest.source37_dichotomy #[``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed] false false true
  checkRoot ``FreyStableLineLocalGlobalTest.source37_cofixed_of_reducible #[``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible] false false false
  checkRoot ``FreyStableLineLocalGlobalTest.source37_irreducible_with_obstruction #[``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_cofixed_obstruction] false false false
  checkRoot ``FreyStableLineLocalGlobalTest.incompatible_local_sides_boundary #[``InertiaLocalGlobalTest.SideBoundary.pointwise_local_alternative,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_fixed,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_cofixed] false false true
  checkInputs ``DkMath.FLT.Frey.Source.residual_inertia_common_side_of_stable #[`S, `hp5, `N, `hN, `hbot, `htop] #[`hbe, `hside, `hlocal, `hcases, `hno, `M, `habs]
  checkInputs ``DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed #[`S, `hp5, `L, `hline, `hstable] #[`hbe, `hside, `hlocal, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_stable_line_cofixed_of_oriented #[`S, `hp5, `hbe, `L, `hline, `hstable] #[`hside, `hcases, `hrat, `hzero, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible #[`S, `hp5, `hbe, `hred] #[`hcases, `hrat, `hzero, `hside, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_cofixed_obstruction #[`S, `hp5, `hbe, `hno] #[`hcases, `hrat, `hzero, `hside, `hred]
  checkInputs ``DkMath.FLT.Frey.Source.residual_not_irreducible_iff_exists_cofixed_line_of_oriented #[`S, `hp5, `hbe] #[`hcases, `hrat, `hzero, `hside, `hred, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.ofCounterexample_residual_exists_cofixed_line #[`p, `hp5, `a, `b, `c, `ha, `hb, `hc, `he] #[`S, `hcases, `hrat, `hzero, `hside, `hno]

#print axioms DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed

#print axioms DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible

#print axioms DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_cofixed_obstruction

end Note031StableLineLocalGlobalDependencyAudit
