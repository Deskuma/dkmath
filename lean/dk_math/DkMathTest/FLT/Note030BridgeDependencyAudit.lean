/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyRationalTorsionBridge
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note030BridgeDependencyAudit"

/-!
# NOTE-030-008: 固定点の降下・有理torsion排除・算術入力の境界の監査

全新規公開宣言の公理と、主要経路の型・opaque本体を走査する。
絶対ガロア固定体、同じ点の基底変換の単射性、030-007の整数核への到達を要求する。
正規化の入口では同じ選択済みSourceと原始化・向き付けの証拠を要求する。
公開型ではhrat/hzeroの外部入力がなく、hcasesとhnoが必要な場所に残ることも検査する。
旧FLT・外部provider・Kummer終点・sorryAxは禁止する。
-/
namespace Note030BridgeDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2M." ||
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
-- 型とopaque本体を含む有限の依存グラフを走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_fixed_eq_zero_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_fixed_submodule_eq_bot_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_isCofixedOn_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_oriented,
    ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_no_cofixed_line,
    ``DkMath.FLT.Frey.Source.ofCounterexample_residual_noNonzeroFixed]
  let regression : Array Name := #[``FreyRationalTorsionBridgeTest.source_thirtySeven_fixed_zero,
    ``FreyRationalTorsionBridgeTest.source_thirtySeven_no_fixed,
    ``FreyRationalTorsionBridgeTest.source_thirtySeven_fixed_submodule,
    ``FreyRationalTorsionBridgeTest.source_thirtySeven_cofixed,
    ``FreyRationalTorsionBridgeTest.source_thirtySeven_conditional_irreducible,
    ``FreyRationalTorsionBridgeTest.counterexample_thirtySeven_profile,
    ``FreyRationalTorsionBridgeTest.actual_two_fixed_boundary,
    ``FreyRationalTorsionBridgeTest.LinearBoundary.diagonal_no_fixed,
    ``FreyRationalTorsionBridgeTest.LinearBoundary.no_fixed_without_dichotomy,
    ``FreyRationalTorsionBridgeTest.LinearBoundary.no_fixed_but_reducible]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented #[``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_iff_rational_torsion,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_rational_torsion_of_fixed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_baseChangePoint_of_fixed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.baseChangePoint_injective,
    ``InfiniteGalois.mem_range_algebraMap_iff_fixed,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_eq_zero_of_oriented #[``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_rational_torsion_of_fixed] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_submodule_eq_bot_of_oriented #[``DkMath.Lib.RepresentationTheory.eq_bot_of_isFixedOn,
    ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_isCofixedOn_of_oriented #[``DkMath.Lib.RepresentationTheory.isCofixedOn_of_fixed_or_cofixed,
    ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_oriented #[``DkMath.FLT.Frey.Source.residual_exists_cofixed_line,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion] false false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_no_cofixed_line #[``DkMath.Lib.RepresentationTheory.isIrreducible_of_no_cofixed_line,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion] false false false
  checkRoot ``DkMath.FLT.Frey.Source.ofCounterexample_residual_noNonzeroFixed #[``DkMath.FLT.Frey.Source.ofCounterexample,
    ``DkMath.FLT.Frey.Source.ofCounterexample_spec,
    ``DkMath.FLT.Frey.PrimitiveReduction,
    ``DkMath.FLT.Frey.OrientationTrace,
    ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented] false false false
  checkRoot ``FreyRationalTorsionBridgeTest.actual_two_fixed_boundary #[``FreyStableLineTest.actual_two_has_fixed,
    ``FreyResidualRepresentationTest.twoPoint_fixed,
    ``FreyResidualRepresentationTest.twoPoint_ne_zero] false false true
  checkRoot ``FreyRationalTorsionBridgeTest.LinearBoundary.no_fixed_without_dichotomy #[``FreyRationalTorsionBridgeTest.LinearBoundary.diagonal_no_fixed,
    ``FreyStableLineTest.DeterminantBoundary.stable_without_dichotomy] true true true
  checkRoot ``FreyRationalTorsionBridgeTest.LinearBoundary.no_fixed_but_reducible #[``FreyRationalTorsionBridgeTest.LinearBoundary.diagonal_no_fixed,
    ``FreyStableLineTest.DeterminantBoundary.line_finrank,
    ``FreyStableLineTest.DeterminantBoundary.line_stable] true true true
  checkInputs ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented #[`hp, `hp5, `hbe]
    #[`hrat, `hzero, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_oriented #[`hp5, `hbe, `hred, `hcases]
    #[`hrat, `hzero]
  checkInputs ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_no_cofixed_line #[`hp5, `hbe, `hcases, `hno]
    #[`hrat, `hzero]

#print axioms DkMath.FLT.Frey.Source.residual_noNonzeroFixed_of_oriented
#print axioms DkMath.FLT.Frey.Source.ofCounterexample_residual_noNonzeroFixed
#print axioms FreyRationalTorsionBridgeTest.LinearBoundary.no_fixed_without_dichotomy

end Note030BridgeDependencyAudit
