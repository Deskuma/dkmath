/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyRationalTorsionIntegral
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note030DependencyAudit"

/-!
# NOTE-030-001〜003: 演算法則・係数・実際の有限軌道の監査

新規公開本体と回帰の公理を検査する。主要経路では型とopaque本体を走査し、
必要な係数bridge・接線計算・有限軌道の最小値を通ることを確認する。
旧FLT終点・外部P2M/P2MW・Kummer終点・sorryAxと、未接続の整数折り返し核を禁止する。
一般付値と有限群論には楕円曲線の定理を借用させない。
今回の監査は付値0の排除や有理torsion排除を証明したことにはならない。
-/
namespace Note030DependencyAudit
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
-- 有限の依存グラフを、型とopaque本体も含めて探索する。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.zero,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.mono,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.neg,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.add,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.sub,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.mul,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.square,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_int,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_nat,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_two,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.valuation_two,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.lower,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.mul,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.square,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.div,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.neg,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.add_lower,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.add_exact,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_lower,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.sub_exact,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.not_lower,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_sub_one_of_unit,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.unit_add_lower,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_add_of_units,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_sub_of_units,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_mul_add_one,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.div_exact,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.ne,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.exact_valuation,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.exact_three,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.exact_two,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.exact_four,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.exact_sixteen,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.pow,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.pow,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.add_min,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.sub_min,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.le_valuation,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.add_exact_of_ne,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_exact_of_ne,
    ``DkMath.Lib.Algebra.FiniteOrbitMinimum.nonnegative_of_strict_drop,
    ``DkMath.Lib.Algebra.FiniteOrbitMinimum.nsmul_nonnegative_of_double_drop,
    ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.equation_of_normalized,
    ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.negY_of_normalized,
    ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.y_integral_of_x_integral,
    ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.y_valuation_of_x_negative,
    ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.double_x_valuation_drop,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_nonzero_of_addOrder_eq,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_nonnegative_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.nsmul_x_nonzero_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_integral_of_prime_order,
    ``DkMath.FLT.Frey.Source.rationalCurve_a₁,
    ``DkMath.FLT.Frey.Source.rationalCurve_a₃,
    ``DkMath.FLT.Frey.Source.rationalCurve_a₆,
    ``DkMath.FLT.Frey.Source.rationalCurve_a₄,
    ``DkMath.FLT.Frey.Source.a₂_twoAdic_integral,
    ``DkMath.FLT.Frey.Source.twoAdicGamma,
    ``DkMath.FLT.Frey.Source.not_two_dvd_a_of_b_even,
    ``DkMath.FLT.Frey.Source.a_odd_of_b_even,
    ``DkMath.FLT.Frey.Source.a_twoAdic_unit,
    ``DkMath.FLT.Frey.Source.b_twoAdic_exact,
    ``DkMath.FLT.Frey.Source.b_twoAdic_positive,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_exact,
    ``DkMath.FLT.Frey.Source.one_le_twoAdicGamma,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_positive,
    ``DkMath.FLT.Frey.Source.x_nonzero_of_addOrder_eq_prime,
    ``DkMath.FLT.Frey.Source.x_nonnegative_of_prime_order,
    ``DkMath.FLT.Frey.Source.nsmul_x_nonzero_of_prime_order,
    ``DkMath.FLT.Frey.Source.x_nonnegative_of_prime_torsion]
  let regression : Array Name := #[``FreyRationalTorsionIntegralTest.zero_boundary,
    ``FreyRationalTorsionIntegralTest.raw_zero_valuation,
    ``FreyRationalTorsionIntegralTest.zero_power_zero,
    ``FreyRationalTorsionIntegralTest.distinct_depth_sum,
    ``FreyRationalTorsionIntegralTest.equal_depth_cancellation,
    ``FreyRationalTorsionIntegralTest.unit_difference_zero,
    ``FreyRationalTorsionIntegralTest.power_thirtySeven,
    ``FreyRationalTorsionIntegralTest.fractional_depth,
    ``FreyRationalTorsionIntegralTest.infinite_drop,
    ``FreyRationalTorsionIntegralTest.actual_source_coefficient,
    ``FreyRationalTorsionIntegralTest.actual_source_a₂,
    ``FreyRationalTorsionIntegralTest.actual_source_b_odd,
    ``FreyRationalTorsionIntegralTest.evenSource,
    ``FreyRationalTorsionIntegralTest.actual_even_coefficient,
    ``FreyRationalTorsionIntegralTest.source_thirtySeven_coefficients,
    ``FreyRationalTorsionIntegralTest.source_thirtySeven_integral,
    ``FreyRationalTorsionIntegralTest.twoCurve,
    ``FreyRationalTorsionIntegralTest.twoCurve_nonsingular,
    ``FreyRationalTorsionIntegralTest.negativeTwoPoint,
    ``FreyRationalTorsionIntegralTest.negative_two_torsion,
    ``FreyRationalTorsionIntegralTest.twoCurve_coefficients,
    ``FreyRationalTorsionIntegralTest.threeCurve,
    ``FreyRationalTorsionIntegralTest.threeCurve_nonsingular,
    ``FreyRationalTorsionIntegralTest.unitThreePoint,
    ``FreyRationalTorsionIntegralTest.unitThreePoint_double,
    ``FreyRationalTorsionIntegralTest.unit_three_torsion,
    ``FreyRationalTorsionIntegralTest.actual_three_orbit,
    ``FreyRationalTorsionIntegralTest.actual_three_nonzero]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_one_sub_one_of_unit #[] true true
  checkRoot ``DkMath.Lib.Algebra.FiniteOrbitMinimum.nsmul_nonnegative_of_double_drop #[``DkMath.Lib.Algebra.FiniteOrbitMinimum.nonnegative_of_strict_drop] true true
  checkRoot ``DkMath.FLT.Frey.Source.a₂_twoAdic_integral #[``DkMath.FLT.Frey.Source.curve_map,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.lower_int] false false
  checkRoot ``DkMath.FLT.Frey.Source.a₄_twoAdic_exact #[``DkMath.FLT.Frey.Source.a_twoAdic_unit,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.exact_sixteen] false false
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.double_x_valuation_drop #[``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.y_valuation_of_x_negative,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.div] true false
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_nonnegative_of_prime_order #[``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.double_x_valuation_drop,
    ``DkMath.Lib.Algebra.FiniteOrbitMinimum.nsmul_nonnegative_of_double_drop,
    ``WeierstrassCurve.Affine.Point.xc] true false
  checkRoot ``DkMath.FLT.Frey.Source.x_nonnegative_of_prime_torsion #[``DkMath.FLT.Frey.Source.a₂_twoAdic_integral,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_positive,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_nonnegative_of_prime_order] false false
  checkRoot ``FreyRationalTorsionIntegralTest.negative_two_torsion #[] true false
  checkRoot ``FreyRationalTorsionIntegralTest.actual_three_orbit #[``DkMath.Lib.Algebra.FiniteOrbitMinimum.nsmul_nonnegative_of_double_drop] true false

#print axioms DkMath.FLT.Frey.Source.a₂_twoAdic_integral
#print axioms DkMath.FLT.Frey.Source.x_nonnegative_of_prime_torsion
#print axioms DkMath.Lib.Algebra.FiniteOrbitMinimum.nonnegative_of_strict_drop

end Note030DependencyAudit
