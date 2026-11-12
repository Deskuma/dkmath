/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilFunction
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note022DependencyAudit"

/-!
# NOTE-022: 点の総和から主イデアルの生成元までの監査

公開宣言と回帰の公理、選択した型とopaque本体の依存経路を検査する。
実際の全射性・有限核・位数公式、一般群の逆元相殺、Point.toClassの単射性を要求する。
主性・生成元・非零性の経路にWeil対データやtorsion基底選択を持ち込むことを禁止する。
一般群の総和補題はDkMathの数論層にも依存しない。付値公式やWeil対の完成の監査ではない。
-/
namespace Note022DependencyAudit
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
    if (algebraOnly && (privateToUserName n).toString.startsWith "DkMath.Lib.NumberTheory.") || (noPairing && ((privateToUserName n).toString.contains "WeilPairingData" ||
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
    ``DkMath.Lib.Algebra.FiniteTorsionSum.sum_eq_zero_of_two_torsion_card_four,
    ``DkMath.Lib.Algebra.FiniteTorsionSum.sum_kernel_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberSet,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_nonempty,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_finite,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_card,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionFinset,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_torsionFinset,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_toFinset_eq_image,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_fiber,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_fiber_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.mem_fiberSet,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.mem_torsionFinset,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.isPrincipal_prod_XYIdeal_zpow_iff,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.pointIdeal,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.pointIdealUnit,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.pointIdeal_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.coe_pointIdealUnit,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.toClass_eq_mk,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.pointIdeal_ne_bot,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.prod_pointIdeal_ne_bot,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.isPrincipal_prod_pointIdealUnit_zpow_iff,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.isPrincipal_prod_pointIdeal_iff,
    ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.pointIdeal_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_ne_bot,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal_iff,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.span_weilNumerator,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.algebraMap_weilNumerator_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction_zero,
    ``DkMath.FLT.Frey.Source.curve_fiber_card,
    ``DkMath.FLT.Frey.Source.curve_fiber_sum,
    ``DkMath.FLT.Frey.Source.curve_fiberIdeal_isPrincipal_iff,
    ``DkMath.FLT.Frey.Source.curve_exists_fiber_generator,
    ``DkMath.FLT.Frey.Source.curve_weilFunction,
    ``DkMath.FLT.Frey.Source.curve_weilFunction_ne_zero]
  let regression : Array Name := #[
    ``FreyWeilFunctionTest.cyclic_two_sum_nonzero,
    ``FreyWeilFunctionTest.target_two_killed,
    ``FreyWeilFunctionTest.actual_two_fiber_nonempty,
    ``FreyWeilFunctionTest.actual_two_fiber_card,
    ``FreyWeilFunctionTest.actual_two_fiber_sum,
    ``FreyWeilFunctionTest.actual_two_fiber_principal,
    ``FreyWeilFunctionTest.actual_two_generator,
    ``FreyWeilFunctionTest.actual_two_function_nonzero,
    ``FreyWeilFunctionTest.actual_37_fiber_card,
    ``FreyWeilFunctionTest.actual_37_fiber_sum,
    ``FreyWeilFunctionTest.one_zero_function,
    ``FreyWeilFunctionTest.infinity_is_unit_ideal,
    ``FreyWeilFunctionTest.actual_point_ideal_not_principal,
    ``FreyWeilFunctionTest.fourPoint,
    ``FreyWeilFunctionTest.fourPoint_double,
    ``FreyWeilFunctionTest.fourPoint_not_two_torsion,
    ``FreyWeilFunctionTest.fourPoint_four_killed,
    ``FreyWeilFunctionTest.non_torsion_target_sum_nonzero,
    ``FreyWeilFunctionTest.non_torsion_target_not_principal]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.Algebra.FiniteTorsionSum.sum_kernel_eq_zero #[``DkMath.Lib.Algebra.FiniteTorsionSum.sum_eq_zero_of_two_torsion_card_four] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_finite #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberEquiv, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_card #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberEquiv] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_torsionFinset #[``DkMath.Lib.Algebra.FiniteTorsionSum.sum_kernel_eq_zero, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_fiber #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_torsionFinset, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_toFinset_eq_image, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_card] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.isPrincipal_prod_pointIdeal_iff #[``WeierstrassCurve.Affine.Point.toClass_eq_zero, ``ClassGroup.mk_eq_one_iff, ``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.toClass_eq_mk] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal_iff #[``DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.isPrincipal_prod_pointIdeal_iff, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_fiber] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal, ``Submodule.IsPrincipal.generator] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator_ne_zero #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.span_weilNumerator, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_ne_bot] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction_ne_zero #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.algebraMap_weilNumerator_ne_zero, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator_ne_zero] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_weilFunction #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction] false true true false
  checkRoot ``FreyWeilFunctionTest.actual_two_generator #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal, ``FreyResidualRepresentationTest.twoPoint] false true true false
  checkRoot ``FreyWeilFunctionTest.non_torsion_target_not_principal #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal_iff, ``FreyWeilFunctionTest.fourPoint_double, ``FreyResidualRepresentationTest.sample] false true true false

end Note022DependencyAudit
