/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilGeometry
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note021DependencyAudit"

/-!
# NOTE-021: 実際の座標環から関数体の平行移動までの依存監査

公開宣言と回帰の公理を検査し、選択した経路では型とopaque本体も辿る。
極大イデアルの分類・局所単項性・DVR、分数体の普遍性と非定数性、合成則を要求する。
幾何学Coreではねじれ点の基底・位数・表現のproviderも禁止する。
WeilPairingData・外部未移植定理・FLT終点・大域Kummer入力は全検査経路で禁止する。
監査はここに列挙した宣言と経路を対象とし、Weil対の存在証明を意味しない。
-/
namespace Note021DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || (#[
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
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.XYIdeal_eq_map,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.mk_mem_XYIdeal_of_evalEval_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.mk_mem_XYIdeal_iff,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isMaximal_XYIdeal,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.XYIdeal_ne_bot,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.span_pair_eq_span_singleton_of_mul_eq,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.map_XYIdeal,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isPrincipal_maximalIdeal_localization,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDiscreteValuationRing_localization_XYIdeal,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isMaximal_of_isPrime_of_ne_bot,
    ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDedekindDomain,
    ``WeierstrassCurve.Affine.Point.xc,
    ``WeierstrassCurve.Affine.Point.yc,
    ``WeierstrassCurve.Affine.Point.nonsingular_xc_yc,
    ``WeierstrassCurve.Affine.Point.eq_some_xc_yc,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.instDecidableEqFunctionField,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericX,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.evalEval_baseChange_polynomial,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.algebraMap_comp_of,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.generic_equation,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.generic_nonsingular,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.eval₂_polynomial_of_point,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_mk,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.coordinateRing_algHom_ext,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.point_xc_map,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.point_yc_map,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_injective_of_ne_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointPull,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_pointPull_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointPull_comp_pointHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_congr,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointPull_comp_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.functionField_algHom_ext,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_surjective,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.evalAt,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.evalAt_mk,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.evalAt_XYIdeal,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_injective,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint_ne_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint_add_baseChange_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint_add_baseChange_ne_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transHom_injective,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_transPull_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_transPull_genericPoint_add,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_comp_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_comp_pointHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_comp_transHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_comp,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_zero,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_apply,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.coe_transEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_genericX,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_genericY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_transEquiv_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_add,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_zero,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_injective,
    ``DkMath.FLT.Frey.Source.geometricCurve_isElliptic,
    ``DkMath.FLT.Frey.Source.geometricCoordinateRing_isDedekindDomain,
    ``DkMath.FLT.Frey.Source.functionFieldTranslation,
    ``DkMath.FLT.Frey.Source.functionFieldTranslation_add,
    ``DkMath.FLT.Frey.Source.functionFieldTranslation_zero,
    ``DkMath.FLT.Frey.Source.functionFieldTranslation_injective]
  let regression : Array Name := #[
    ``FreyWeilGeometryTest.actual_dedekind,
    ``FreyWeilGeometryTest.actual_local_dvr,
    ``FreyWeilGeometryTest.actual_generic_not_constant,
    ``FreyWeilGeometryTest.shiftPoint,
    ``FreyWeilGeometryTest.shiftPoint_ne_zero,
    ``FreyWeilGeometryTest.shiftPoint_add_self,
    ``FreyWeilGeometryTest.actual_translation_nonidentity,
    ``FreyWeilGeometryTest.actual_translation_square,
    ``FreyWeilGeometryTest.actual_translation_moves_generic,
    ``FreyWeilGeometryTest.constant_evaluation_not_injective,
    ``FreyWeilGeometryTest.actual_place_nonzero,
    ``FreyWeilGeometryTest.actual_places_covered]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDedekindDomain #[``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal, ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isPrincipal_maximalIdeal_localization, ``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDiscreteValuationRing_localization_XYIdeal] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_injective_of_ne_baseChange #[``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointPull #[``IsFractionRing.liftAlgHom] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint_ne_baseChange, ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_injective_of_ne_baseChange, ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_comp, ``DkMath.Lib.NumberTheory.EllipticFunctionField.transPull_zero] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_injective #[``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_genericX, ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_genericY] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_surjective #[``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isMaximal_iff_exists_eq_XYIdeal] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_injective #[``DkMath.Lib.NumberTheory.EllipticFunctionField.evalAt_XYIdeal] true true true true
  checkRoot ``DkMath.FLT.Frey.Source.functionFieldTranslation #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv] false true true true
  checkRoot ``FreyWeilGeometryTest.actual_local_dvr #[``DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDiscreteValuationRing_localization_XYIdeal, ``FreyResidualRepresentationTest.sample] false true true false
  checkRoot ``FreyWeilGeometryTest.actual_translation_nonidentity #[``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_injective, ``FreyResidualRepresentationTest.twoPoint] false true true false
  checkRoot ``FreyWeilGeometryTest.actual_translation_square #[``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_add, ``FreyResidualRepresentationTest.twoPoint] false true true false
  checkRoot ``FreyWeilGeometryTest.constant_evaluation_not_injective #[``WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero, ``DkMath.Lib.NumberTheory.EllipticFunctionField.evalAt_mk] false true true false

end Note021DependencyAudit
