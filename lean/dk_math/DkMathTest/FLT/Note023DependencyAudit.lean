/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilValuation
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note023DependencyAudit"

/-!
# NOTE-023: 同じ座標環と関数の有限点付値を測る経路の監査

公開宣言と回帰の公理、選択した型とopaque本体の依存経路を検査する。
二乗では割れないことを示す素イデアル積の議論、実際のDedekind性、既存の生成イデアル等式を要求する。
商から整数位数へは、非零性とlogの商の法則を要求する。
一般の点イデアルの測定にはtorsion表現providerすら不要である。
Weil対データ・torsion基底選択・外部未移植定理・FLT終点・大域Kummer入力は禁止する。
無限遠点・付値輸送・非退化性を証明したと解釈しない。
-/
namespace Note023DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || (#[
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionBasis,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerBasis]).contains n || (#[
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_of_card_sq,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_standard_card_sq,
    `DkMath.FLT.Frey.Source.residual_profile_of_card_sq,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_prime_sq_of_prime_lt,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_of_prime_lt,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_two,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two]).contains n || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
    s.startsWith "P2M." || s.startsWith "FreyPackage." || s.contains "fermat_last_theorem" ||
    s.toLower.contains "herbrand" || s.toLower.contains "ribet" ||
    s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
    s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution"

private def globalProvider (n : Name) : Bool :=
  (#[`DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt,
    `DkMath.Lib.NumberTheory.KummerUnitPowerCriterion,
    `DkMath.FLT.Kummer.RegularDescent.Conditions,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_quotient_roots,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_descent_roots,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_weighted_successor,
    `DkMath.FLT.Kummer.RegularDescent.descent_step,
    `DkMath.FLT.Kummer.RegularDescent.no_state,
    `DkMath.FLT.Kummer.RegularDescent.ratio_power,
    `DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    `DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt]).any (fun root => root.isPrefixOf n)

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) (localOnly : Bool := false) (noPairing : Bool := false) (algebraOnly : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if (algebraOnly && (`DkMath.Lib.NumberTheory.EllipticTorsionRepresentation).isPrefixOf (privateToUserName n)) || (noPairing && ((privateToUserName n).toString.contains "WeilPairingData" ||
        (`DkMath.Lib.NumberTheory.RootPairing).isPrefixOf (privateToUserName n))) || forbidden n || (localOnly && globalProvider (privateToUserName n)) ||
        (neutral && (privateToUserName n).toString.startsWith "DkMath.FLT.") then throwError "Forbidden dependency: {n}"
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
-- 型とopaque本体を含む有限の依存グラフを探索するための上限解除。
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.pointIdeal_eq_placeOf,
    ``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_of_span_eq_prod,
    ``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_generator_independent,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricCoordinateRing_isDedekindDomain,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointOrder,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointOrder_div,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilNumerator,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilNumerator,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilFunction,
    ``DkMath.FLT.Frey.Source.curve_weilNumerator_order,
    ``DkMath.FLT.Frey.Source.curve_weilFunction_valuation,
    ``DkMath.FLT.Frey.Source.curve_weilFunction_order]
  let regression : Array Name := #[
    ``FreyWeilValuationTest.twoPoint_val_ne_zero,
    ``FreyWeilValuationTest.fourPoint_ne_zero,
    ``FreyWeilValuationTest.numerator,
    ``FreyWeilValuationTest.numerator_ne_zero,
    ``FreyWeilValuationTest.actual_simple_zero_value,
    ``FreyWeilValuationTest.actual_simple_zero_order,
    ``FreyWeilValuationTest.denominator_off_zero_fiber,
    ``FreyWeilValuationTest.actual_function_simple_zero,
    ``FreyWeilValuationTest.denominator_simple_zero,
    ``FreyWeilValuationTest.numerator_off_target_fiber,
    ``FreyWeilValuationTest.actual_function_simple_pole,
    ``FreyWeilValuationTest.liftPoint,
    ``FreyWeilValuationTest.liftPoint_double,
    ``FreyWeilValuationTest.liftPoint_ne_zero,
    ``FreyWeilValuationTest.fourPoint_ne_target,
    ``FreyWeilValuationTest.actual_function_off_both,
    ``FreyWeilValuationTest.zero_target_cancels,
    ``FreyWeilValuationTest.one_zero_target_order,
    ``FreyWeilValuationTest.thirtySeven_zero_target_order,
    ``FreyWeilValuationTest.arbitrary_generator_same_local_value]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_of_span_eq_prod #[``IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, ``Ideal.IsPrime.prod_le, ``mul_dvd_mul_iff_left, ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_injective] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_generator_independent #[``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_of_span_eq_prod] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricCoordinateRing_isDedekindDomain #[``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDedekindDomain] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricCoordinateRing_isDedekindDomain, ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf, ``IsDedekindDomain.HeightOneSpectrum.valuation] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointOrder_div #[``WithZero.log_div, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation_ne_zero] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilNumerator #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.span_weilNumerator, ``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_of_span_eq_prod, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricCoordinateRing_isDedekindDomain] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilFunction #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilNumerator, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilNumerator #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilNumerator, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointOrder] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilFunction #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointOrder_div, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilNumerator, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.algebraMap_weilNumerator_ne_zero] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_weilFunction_order #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilFunction, ``DkMath.FLT.Frey.Source.curve_weilFunction] false true true false
  checkRoot ``FreyWeilValuationTest.actual_function_simple_zero #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilFunction, ``FreyWeilFunctionTest.fourPoint_double, ``FreyResidualRepresentationTest.sample] false true true false
  checkRoot ``FreyWeilValuationTest.actual_function_simple_pole #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilFunction, ``FreyWeilFunctionTest.target_two_killed, ``FreyResidualRepresentationTest.twoPoint] false true true false
  checkRoot ``FreyWeilValuationTest.arbitrary_generator_same_local_value #[``DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_generator_independent, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.span_weilNumerator] false true true false

end Note023DependencyAudit
