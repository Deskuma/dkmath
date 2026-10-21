/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyRationalTorsionPositive
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note030PositiveDependencyAudit"

/-!
# NOTE-030-004: 正の付値へ進む経路の監査

新規本体・回帰の公理を検査し、主要経路では型とopaque本体も走査する。
係数の偶奇、倍点の単元性、割線の負付値、前章の有限軌道による非負下界を要求する。
旧FLT・外部provider・Kummer終点・sorryAx・未接続の整数折り返し核を禁止する。
実在する5-torsionを検査するが、Frey Sourceや一般FLTの反例とは見なさない。
-/
namespace Note030PositiveDependencyAudit
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
          s.startsWith "DkMath.Lib.NumberTheory.Weierstrass" ||
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
  let production : Array Name := #[``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.not_unit_x_of_even_a₂,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.double_x_unit,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.triple_x_valuation_negative,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.x_positive_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.nsmul_x_positive_of_prime_order,
    ``DkMath.FLT.Frey.Source.x_positive_of_prime_order,
    ``DkMath.FLT.Frey.Source.nsmul_x_positive_of_prime_order,
    ``DkMath.FLT.Frey.Source.nsmul_x_positive_of_prime_torsion,
    ``DkMath.FLT.Frey.Source.orbit_x_lower_bound]
  let regression : Array Name := #[``FreyRationalTorsionPositiveTest.three_is_boundary,
    ``FreyRationalTorsionPositiveTest.three_double_unit,
    ``FreyRationalTorsionPositiveTest.three_double_x_equal,
    ``FreyRationalTorsionPositiveTest.secantCurve,
    ``FreyRationalTorsionPositiveTest.secantCurve_nonsingular,
    ``FreyRationalTorsionPositiveTest.unitPoint,
    ``FreyRationalTorsionPositiveTest.secantDouble_nonsingular,
    ``FreyRationalTorsionPositiveTest.unitPoint_double,
    ``FreyRationalTorsionPositiveTest.unitPoint_triple_x,
    ``FreyRationalTorsionPositiveTest.actual_triple_negative,
    ``FreyRationalTorsionPositiveTest.fiveCurve,
    ``FreyRationalTorsionPositiveTest.fiveCurve_nonsingular,
    ``FreyRationalTorsionPositiveTest.fivePoint,
    ``FreyRationalTorsionPositiveTest.fiveDouble_nonsingular,
    ``FreyRationalTorsionPositiveTest.fiveDouble,
    ``FreyRationalTorsionPositiveTest.fivePoint_double,
    ``FreyRationalTorsionPositiveTest.fiveDouble_double,
    ``FreyRationalTorsionPositiveTest.fivePoint_order,
    ``FreyRationalTorsionPositiveTest.fiveCurve_coefficients,
    ``FreyRationalTorsionPositiveTest.actual_five_orbit_positive,
    ``FreyRationalTorsionPositiveTest.zero_multiple_boundary,
    ``FreyRationalTorsionPositiveTest.source_thirtySeven_lower_bound]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.not_unit_x_of_even_a₂ #[``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_add_of_units] true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.double_x_unit #[``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_mul_add_one,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.div_exact] true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.triple_x_valuation_negative #[``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_sub_of_units,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.div] true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.x_positive_of_prime_order #[``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.not_unit_x_of_even_a₂,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.double_x_unit,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.triple_x_valuation_negative,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_nonnegative_of_prime_order] true
  checkRoot ``DkMath.FLT.Frey.Source.orbit_x_lower_bound #[``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.nsmul_x_positive_of_prime_order,
    ``DkMath.FLT.Frey.Source.a₂_twoAdic_integral,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_positive] false
  checkRoot ``FreyRationalTorsionPositiveTest.actual_triple_negative #[``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.triple_x_valuation_negative] true
  checkRoot ``FreyRationalTorsionPositiveTest.actual_five_orbit_positive #[``FreyRationalTorsionPositiveTest.fivePoint_order,
    ``FreyRationalTorsionPositiveTest.fivePoint_double,
    ``FreyRationalTorsionPositiveTest.fiveDouble_double,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.x_positive_of_prime_order] true

#print axioms DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.x_positive_of_prime_order
#print axioms DkMath.FLT.Frey.Source.orbit_x_lower_bound
#print axioms FreyRationalTorsionPositiveTest.actual_five_orbit_positive

end Note030PositiveDependencyAudit
