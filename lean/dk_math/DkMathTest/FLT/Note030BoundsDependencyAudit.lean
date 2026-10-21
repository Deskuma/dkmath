/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyRationalTorsionBounds
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note030BoundsDependencyAudit"

/-!
# NOTE-030-005: 反射と上下界の依存監査

全新規公開宣言の公理を検査し、主要経路は型とopaque本体まで走査する。
反射の実際の加法公式、2T=0、負付値の降下、単元例外の排除、元の2Qの下界、
Sourceの正確な係数付値への到達を要求する。整数折り返し核や外部のFLT終点は使わない。
-/
namespace Note030BoundsDependencyAudit
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
  let production : Array Name := #[``DkMath.Lib.NumberTheory.WeierstrassXReflection.origin_nonsingular,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.twoTorsionPoint_ne_zero,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.two_nsmul_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.add_twoTorsionPoint_twice,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.double_add_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.odd_nsmul_add_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.addX_origin,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.add_twoTorsionPoint_x,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.add_twoTorsionPoint_ne_zero,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.valuation_add_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.exact_add_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_below_gamma_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_bounds_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.nsmul_x_bounds_of_prime_order,
    ``DkMath.FLT.Frey.Source.rationalTwoTorsionPoint,
    ``DkMath.FLT.Frey.Source.x_reflection_by_two_torsion,
    ``DkMath.FLT.Frey.Source.x_below_gamma_of_prime_order,
    ``DkMath.FLT.Frey.Source.nsmul_x_bounds_of_prime_order,
    ``DkMath.FLT.Frey.Source.nsmul_x_bounds_of_prime_torsion,
    ``DkMath.FLT.Frey.Source.orbit_x_bounds]
  let regression : Array Name := #[``FreyRationalTorsionBoundsTest.fiveCurve_a₄_exact,
    ``FreyRationalTorsionBoundsTest.fiveT,
    ``FreyRationalTorsionBoundsTest.fiveT_order_two,
    ``FreyRationalTorsionBoundsTest.actual_translation_laws,
    ``FreyRationalTorsionBoundsTest.actual_reflected_x,
    ``FreyRationalTorsionBoundsTest.actual_reflected_depth,
    ``FreyRationalTorsionBoundsTest.actual_translated_five_multiple,
    ``FreyRationalTorsionBoundsTest.translated_not_five_torsion,
    ``FreyRationalTorsionBoundsTest.actual_five_orbit_bounds,
    ``FreyRationalTorsionBoundsTest.upper_bound_attained,
    ``FreyRationalTorsionBoundsTest.origin_translation_boundary,
    ``FreyRationalTorsionBoundsTest.source_thirtySeven_bounds]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXReflection.add_twoTorsionPoint_x #[``DkMath.Lib.NumberTheory.WeierstrassXReflection.addX_origin,
    ``WeierstrassCurve.Affine.Point.add_of_X_ne] true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXReflection.double_add_twoTorsionPoint #[``DkMath.Lib.NumberTheory.WeierstrassXReflection.two_nsmul_twoTorsionPoint] true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassXReflection.exact_add_twoTorsionPoint #[``DkMath.Lib.NumberTheory.WeierstrassXReflection.add_twoTorsionPoint_x,
    ``DkMath.Lib.NumberTheory.RationalTwoAdicBounds.Exact.div] true
  checkRoot ``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_below_gamma_of_prime_order #[``DkMath.Lib.NumberTheory.WeierstrassXReflection.exact_add_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.double_add_twoTorsionPoint,
    ``DkMath.Lib.NumberTheory.WeierstrassNegativeValuation.double_x_valuation_drop,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.not_unit_x_of_even_a₂,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.double_x_unit,
    ``DkMath.Lib.NumberTheory.WeierstrassPositiveValuation.nsmul_x_positive_of_prime_order,
    ``DkMath.Lib.NumberTheory.WeierstrassTorsionValuation.x_nonnegative_of_prime_order] true
  checkRoot ``DkMath.FLT.Frey.Source.orbit_x_bounds #[``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.nsmul_x_bounds_of_prime_order,
    ``DkMath.FLT.Frey.Source.a₄_twoAdic_exact,
    ``DkMath.FLT.Frey.Source.one_le_twoAdicGamma,
    ``DkMath.FLT.Frey.Source.a₂_twoAdic_integral] false
  checkRoot ``FreyRationalTorsionBoundsTest.actual_five_orbit_bounds #[``DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_below_gamma_of_prime_order,
    ``FreyRationalTorsionPositiveTest.fivePoint_order,
    ``FreyRationalTorsionBoundsTest.fiveCurve_a₄_exact] true
  checkRoot ``FreyRationalTorsionBoundsTest.translated_not_five_torsion #[``DkMath.Lib.NumberTheory.WeierstrassXReflection.odd_nsmul_add_twoTorsionPoint,
    ``FreyRationalTorsionPositiveTest.fivePoint_order,
    ``DkMath.Lib.NumberTheory.WeierstrassXReflection.twoTorsionPoint_ne_zero] true

#print axioms DkMath.Lib.NumberTheory.WeierstrassTorsionBounds.x_below_gamma_of_prime_order
#print axioms DkMath.FLT.Frey.Source.orbit_x_bounds
#print axioms FreyRationalTorsionBoundsTest.actual_five_orbit_bounds

end Note030BoundsDependencyAudit
