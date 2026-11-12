/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyRationalTorsionIdentities
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note030IdentitiesDependencyAudit"

/-!
# NOTE-030-006: 恒等式・非零ガード・実際の座標の依存監査

全新規公開宣言の公理と、主要経路の型・opaque本体を走査する。
可換環の多項式核が幾何を使わないこと、付値化が実際の加法公式と非零性を通ること、
軌道とSourceの入力が既存の区間定理に到達することを検査する。
整数核や外部のFLT終点はまだ使わない。位数4の境界例と位数5の回帰も検査する。
-/
namespace Note030IdentitiesDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit." || s.startsWith "FltRegular." || s.startsWith "P2M." ||
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

set_option maxHeartbeats 0 in
-- 型とopaque本体を含む有限の依存グラフを走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_polynomial_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.double_addX_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_addX_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.double_x_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_x_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.tangent_denominator_exact,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.double_x_valuation_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_x_valuation_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.nsmul_x_ne_x_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.tangent_denominator_exact_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.double_x_valuation_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order,
    ``DkMath.FLT.Frey.Source.tangent_denominator_exact_of_prime_torsion,
    ``DkMath.FLT.Frey.Source.double_x_valuation_identity,
    ``DkMath.FLT.Frey.Source.plus_minus_x_valuation_identity]
  let regression : Array Name := #[``FreyRationalTorsionIdentitiesTest.integer_polynomial_example,
    ``FreyRationalTorsionIdentitiesTest.actual_tangent_depth,
    ``FreyRationalTorsionIdentitiesTest.actual_double_identity,
    ``FreyRationalTorsionIdentitiesTest.actual_double_numerator_depth,
    ``FreyRationalTorsionIdentitiesTest.actual_five_interior,
    ``FreyRationalTorsionIdentitiesTest.actual_secant_numerator_depth,
    ``FreyRationalTorsionIdentitiesTest.endpoint_x_coincides,
    ``FreyRationalTorsionIdentitiesTest.fourCurve,
    ``FreyRationalTorsionIdentitiesTest.fourCurve_nonsingular,
    ``FreyRationalTorsionIdentitiesTest.fourPoint,
    ``FreyRationalTorsionIdentitiesTest.four_point_boundary,
    ``FreyRationalTorsionIdentitiesTest.four_point_order,
    ``FreyRationalTorsionIdentitiesTest.source_thirtySeven_double,
    ``FreyRationalTorsionIdentitiesTest.source_thirtySeven_interior]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_polynomial_identity #[] true true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.tangent_denominator_exact #[``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.equation_of_normalized,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.add_lower] true false
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.double_x_identity #[``DkMath.Lib.NumberTheory.WeierstrassXIdentities.double_addX_identity,
    ``WeierstrassCurve.Affine.Point.add_self_of_Y_ne] true false
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_x_identity #[``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_polynomial_identity,
    ``WeierstrassCurve.Affine.Point.add_of_X_ne,
    ``WeierstrassCurve.Affine.Point.neg_some] true false
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.double_x_valuation_of_prime_order #[``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.tangent_denominator_exact_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_bounds_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.nsmul_x_nonzero_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.double_x_valuation_identity] true false
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order #[``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.nsmul_x_ne_x_of_prime_order,
    ``WeierstrassCurve.Affine.Point.X_eq_iff,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.nsmul_x_nonzero_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_x_valuation_identity,
    ``DkMath.Lib.NumberTheory.WeierstrassXIdentities.plus_minus_x_identity] true false
  checkRoot ``DkMath.FLT.Frey.Source.double_x_valuation_identity #[``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.double_x_valuation_of_prime_order,
    ``DkMath.FLT.Frey.Source.a₂_twoAdic_integral,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_exact,
    ``DkMath.FLT.Frey.Source.one_le_twoAdicGamma] false false
  checkRoot ``DkMath.FLT.Frey.Source.plus_minus_x_valuation_identity #[``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order] false false
  checkRoot ``FreyRationalTorsionIdentitiesTest.actual_five_interior #[``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order,
    ``FreyRationalTorsionPositiveTest.fivePoint_order] true false
  checkRoot ``FreyRationalTorsionIdentitiesTest.four_point_order #[``FreyRationalTorsionIdentitiesTest.four_point_boundary,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.twoTorsionPoint_ne_zero,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.two_nsmul_twoTorsionPoint] true false

#print axioms DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.double_x_valuation_of_prime_order
#print axioms DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order
#print axioms DkMath.FLT.Frey.Source.plus_minus_x_valuation_identity

end Note030IdentitiesDependencyAudit
