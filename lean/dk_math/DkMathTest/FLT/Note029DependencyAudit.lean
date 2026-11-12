/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyStableLine
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note029DependencyAudit"

/-!
# NOTE-029: 新規本体・回帰の依存監査

全ての名前付き定義・定理について標準三公理だけを許す。
主要経路では型とopaque本体も走査し、旧FLT終点・外部provider・sorryAxを禁止する。
一般代数・整数漸化式はFreyや楕円曲線の定理を借用しない。
条件付き定理を監査しても、その引数である二択・有理torsion排除を証明したことにはならない。
-/
namespace Note029DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2M." ||
    s.startsWith "P2MW." || s.startsWith "FreyPackage." ||
    s.contains "fermatLastTheorem" || s.contains "fermat_last_theorem" ||
    s.contains "fermatThree_no_positive_solution" ||
    (`DkMath.FLT.Kummer).isPrefixOf (privateToUserName n)

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false)
    (algebraOnly : Bool := false) : CommandElabM Unit := do
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
        (algebraOnly && s.startsWith "DkMath.Lib.NumberTheory.Elliptic") then
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

set_option maxHeartbeats 0 in
-- 有限の依存グラフを、型とopaque本体も含めて探索する。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.RepresentationTheory.IsFixedOn,
    ``DkMath.Lib.RepresentationTheory.IsCofixedOn,
    ``DkMath.Lib.RepresentationTheory.NoNonzeroFixed,
    ``DkMath.Lib.RepresentationTheory.IsFixedOn.isStable,
    ``DkMath.Lib.RepresentationTheory.IsCofixedOn.isStable,
    ``DkMath.Lib.RepresentationTheory.isCofixedOn_iff_mkQ,
    ``DkMath.Lib.RepresentationTheory.eq_bot_of_isFixedOn,
    ``DkMath.Lib.RepresentationTheory.isCofixedOn_of_fixed_or_cofixed,
    ``DkMath.Lib.RepresentationTheory.exists_stable_line_of_not_isIrreducible,
    ``DkMath.Lib.RepresentationTheory.exists_cofixed_line_of_not_isIrreducible,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_of_no_cofixed_line,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.baseChangePointHom,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.baseChangePoint_injective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_baseChangePoint_of_fixed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_rational_torsion_of_fixed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointSubgroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointSubgroupEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_pointSubgroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isAddCyclic_pointSubgroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointSubgroup_killed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointSubgroup_stable,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_stable_pointSubgroup_of_reducible,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_cofixed_line_of_reducible,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.prime_not_dvd_modulus,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.cancel_prime_modulus,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_folded_valuation_orbit,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit,
    ``DkMath.FLT.Frey.Source.residual_exists_stable_pointSubgroup,
    ``DkMath.FLT.Frey.Source.residual_noNonzeroFixed_iff_rational_torsion,
    ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line,
    ``DkMath.FLT.Frey.Source.residual_isIrreducible_of_no_cofixed_line,
    ``DkMath.FLT.Frey.Source.residual_stable_line_diagonal_product,
    ``DkMath.FLT.Frey.Source.residual_valuation_modulus_cancel]
  let regression : Array Name := #[``FreyStableLineTest.actual_two_subgroup,
    ``FreyStableLineTest.actual_thirtySeven_card,
    ``FreyStableLineTest.actual_two_descends,
    ``FreyStableLineTest.actual_two_has_fixed,
    ``FreyStableLineTest.actual_thirtySeven_fixed_iff,
    ``FreyStableLineTest.cancel_thirtySeven,
    ``FreyStableLineTest.cancellation_fails_at_two,
    ``FreyStableLineTest.DeterminantBoundary.action,
    ``FreyStableLineTest.DeterminantBoundary.rho,
    ``FreyStableLineTest.DeterminantBoundary.line,
    ``FreyStableLineTest.DeterminantBoundary.line_eq_span,
    ``FreyStableLineTest.DeterminantBoundary.line_finrank,
    ``FreyStableLineTest.DeterminantBoundary.line_stable,
    ``FreyStableLineTest.DeterminantBoundary.determinant,
    ``FreyStableLineTest.DeterminantBoundary.line_not_fixed,
    ``FreyStableLineTest.DeterminantBoundary.line_not_cofixed,
    ``FreyStableLineTest.DeterminantBoundary.stable_without_dichotomy]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.RepresentationTheory.exists_cofixed_line_of_not_isIrreducible #[``DkMath.Lib.RepresentationTheory.exists_stable_line_of_not_isIrreducible,
    ``DkMath.Lib.RepresentationTheory.isCofixedOn_of_fixed_or_cofixed] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_stable_pointSubgroup_of_reducible #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointSubgroupEquiv,
    ``Module.natCard_eq_pow_finrank] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion #[``InfiniteGalois.mem_range_algebraMap_iff_fixed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.baseChangePoint_injective] true false
  checkRoot ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit #[``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_folded_valuation_orbit,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.cancel_prime_modulus] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_stable_pointSubgroup #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_stable_pointSubgroup_of_reducible] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_cofixed_line #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion,
    ``DkMath.Lib.RepresentationTheory.exists_cofixed_line_of_not_isIrreducible] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_stable_line_diagonal_product #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData] false false
  checkRoot ``FreyStableLineTest.DeterminantBoundary.stable_without_dichotomy #[] true true
  checkRoot ``FreyStableLineTest.DeterminantBoundary.determinant #[] true true

#print axioms DkMath.FLT.Frey.Source.residual_exists_stable_pointSubgroup
#print axioms DkMath.FLT.Frey.Source.residual_exists_cofixed_line
#print axioms DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit

end Note029DependencyAudit
