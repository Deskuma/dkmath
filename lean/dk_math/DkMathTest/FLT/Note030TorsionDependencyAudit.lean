/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyRationalTorsion
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note030TorsionDependencyAudit"

/-!
# NOTE-030-007: 実際の軌道から有理torsion排除への全経路の監査

新規宣言の公理を検査し、主要経路は型とopaque本体まで走査する。
今回初めて整数折り返し核を必須経路として要求する。実際の点の座標、
非零因子のmin条件、倍点・和差、端点、素数約分、Sourceの係数供給を全て要求する。
一般の位数5の回帰は整数核を使わず七条件を満たすことも検査する。
旧FLT・外部provider・Kummer終点・sorryAxは禁止し、hratの接続は行わない。
-/
namespace Note030TorsionDependencyAudit
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

set_option maxHeartbeats 0 in
-- 型とopaque本体を含む有限の依存グラフを走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_valuation_spec,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.xValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.productGapValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.differenceValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.squareGapValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.OrbitConditions,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.xValuation_endpoint,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.orbit_conditions,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.no_prime_shifted_torsion,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.prime_torsion_eq_zero,
    ``DkMath.FLT.Frey.Source.valuationOrbit_conditions,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero,
    ``DkMath.FLT.Frey.Source.rational_p_torsion_iff]
  let regression : Array Name := #[``FreyRationalTorsionTest.equal_depth_nonzero_difference,
    ``FreyRationalTorsionTest.zero_difference_guard,
    ``FreyRationalTorsionTest.actual_five_orbit_conditions,
    ``FreyRationalTorsionTest.actual_five_sequence_values,
    ``FreyRationalTorsionTest.actual_five_endpoint,
    ``FreyRationalTorsionTest.five_shifted_shape_fails,
    ``FreyRationalTorsionTest.five_modulus_cancellation_fails,
    ``FreyRationalTorsionTest.shiftedCurve,
    ``FreyRationalTorsionTest.shifted_curve_has_two_torsion,
    ``FreyRationalTorsionTest.shifted_curve_five_torsion,
    ``FreyRationalTorsionTest.shifted_curve_zero_point,
    ``FreyRationalTorsionTest.source_thirtySeven_torsion,
    ``FreyRationalTorsionTest.source_thirtySeven_iff]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_valuation_spec #[``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_exact_of_ne,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Lower.le_valuation] true true true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.xValuation_endpoint #[``WeierstrassCurve.Affine.Point.neg] true false true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.orbit_conditions #[``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.xValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.productGapValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.differenceValuation,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.squareGapValuation,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_valuation_spec,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.nsmul_x_bounds_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.double_x_valuation_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.xValuation_endpoint] true false true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.no_prime_shifted_torsion #[``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.orbit_conditions,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.cancel_prime_modulus,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_folded_valuation_orbit] true false false
  checkRoot ``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero #[``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.prime_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.no_prime_shifted_torsion,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.sub_valuation_spec,
    ``DkMath.FLT.Frey.Source.a₂_twoAdic_integral,
    ``DkMath.FLT.Frey.Source.curve_map,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_exact,
    ``DkMath.FLT.Frey.Source.not_two_dvd_a_of_b_even,
    ``DkMath.FLT.Frey.Source.one_le_twoAdicGamma] false false false
  checkRoot ``FreyRationalTorsionTest.actual_five_orbit_conditions #[``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.orbit_conditions,
    ``FreyRationalTorsionPositiveTest.fivePoint_order] true false true
  checkRoot ``FreyRationalTorsionTest.shifted_curve_five_torsion #[``DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.prime_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit] true false false
  checkRoot ``FreyRationalTorsionTest.source_thirtySeven_torsion #[``DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero,
    ``DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit] false false false

#print axioms DkMath.Lib.NumberTheory.WeierstrassValuationOrbit.prime_torsion_eq_zero
#print axioms DkMath.FLT.Frey.Source.rational_p_torsion_eq_zero
#print axioms FreyRationalTorsionTest.actual_five_orbit_conditions

end Note030TorsionDependencyAudit
