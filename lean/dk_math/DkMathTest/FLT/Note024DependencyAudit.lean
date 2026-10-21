/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilTransport
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note024DependencyAudit"

/-!
# NOTE-024: 次数と無限遠点を含む輸送の証明経路
新規の名前付き本体宣言・回帰宣言を列挙し、標準論理公理以外への依存を検査する。
選択した型とopaque本体ではCRT・実際の分数体付値・付値環の分類・正規化の経路を要求する。
外部未移植provider、Weil対データ、既存FLT終点、大域Kummer入力を禁止する。
-/
namespace Note024DependencyAudit
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
    ``Valuation.eq_of_valuationSubring_eq_aux,
    ``Valuation.valuationSubring_comap,
    ``Valuation.eq_comap_of_valuationSubring_le_comap_aux,
    ``DkMath.Lib.NumberTheory.EllipticPointIdealNorm.finrank_quotient_pointIdeal,
    ``DkMath.Lib.NumberTheory.EllipticPointIdealNorm.natDegree_norm_of_span_eq_prod,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.norm_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.valuationInftyDef,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.degree_norm_add_le,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.valuationInftyInt,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.valuationInftyInt_apply,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.nonZeroDivisors_le_supp_primeCompl,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.valuationInfty,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.valuationInfty_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.mk_Y_mul_mk_Y_add,
    ``Valuation.map_aeval_eq_pow_of_one_lt,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.FunctionField.algebraMap_mk_C_C,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.FunctionField.algebraMap_mk_C,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.FunctionField.valuation_algebraMap_K,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.FunctionField.valuation_algebraMap_sq,
    ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.FunctionField.eq_valuationSubring_of_X_not_mem_aux,
    ``Valuation.Cong,
    ``Valuation.cong_iff,
    ``Valuation.Cong.refl,
    ``Valuation.Cong.rfl,
    ``Valuation.Cong.symm,
    ``Valuation.Cong.trans,
    ``Valuation.Cong.add,
    ``Valuation.Cong.neg,
    ``Valuation.Cong.sub,
    ``Valuation.Cong.le_one,
    ``Valuation.Cong.mul,
    ``Valuation.Cong.pow,
    ``Valuation.Cong.eq_of_eq_one,
    ``Valuation.Cong.lt_one_iff,
    ``Valuation.cong_zero_iff,
    ``Valuation.Cong.inv,
    ``Valuation.Cong.div,
    ``Valuation.Cong.eval₂,
    ``Valuation.Cong.eval₂_eval₂,
    ``IsDedekindDomain.HeightOneSpectrum.valuation_map_le_exp_neg_of_mem_pow,
    ``IsDedekindDomain.HeightOneSpectrum.valuation_map_le_of_valuation_le,
    ``WithZero.lt_one_iff_le_exp_neg_one,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_algebraMap_le_one,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_algebraMap_eq_one,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.mem_placeOf_iff,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.cong_genericX,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.cong_genericY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.algebraMap_evalEval,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_mk_eq_eval₂,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_pointPull_le,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.genericX_ne_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.baseChange_a_eq,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.cong_addX_addY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_le',
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.wAtY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.eval_wAtY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.eval_derivative_wAtY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.eval₂_wAtY_generic,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_le_self',
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_eq,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.InfinityCoordinateRing.natDegree_norm_mk_C',
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.InfinityCoordinateRing.natDegree_norm_mk_Y',
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.InfinityCoordinateRing.mk_Y_ne_zero',
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.InfinityCoordinateRing.mk_C_X_ne_zero',
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_XClass_lt_valuation_YClass,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.one_lt_valuation_transEquiv_genericX,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_placeOf_neg_transEquiv_algebraMap_aux,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_placeOf_neg_transEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.normDegree_weilNumerator_balance,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.normDegree_weilNumerator,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.infinityOrder,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.infinityOrder_weilNumerator,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.infinityOrder_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_neg_apply,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_transEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_eq_neg_log,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_transEquiv_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction_of_torsion,
    ``DkMath.FLT.Frey.Source.curve_weilNumerator_normDegree,
    ``DkMath.FLT.Frey.Source.curve_weilFunction_pointOrder,
    ``DkMath.FLT.Frey.Source.curve_weilFunction_pointOrder_transEquiv]
  let regression : Array Name := #[
    ``FreyWeilTransportTest.normDegree_nonzero_target,
    ``FreyWeilTransportTest.normDegree_zero_target,
    ``FreyWeilTransportTest.normDegree_one,
    ``FreyWeilTransportTest.normDegree_thirtySeven,
    ``FreyWeilTransportTest.numerator_infinity_order,
    ``FreyWeilTransportTest.actual_infinity_pole,
    ``FreyWeilTransportTest.infinity_zero_target_cancels,
    ``FreyWeilTransportTest.target_add_self,
    ``FreyWeilTransportTest.exceptional_translation_pole,
    ``FreyWeilTransportTest.infinity_translation_pole,
    ``FreyWeilTransportTest.regular_translation_zero,
    ``FreyWeilTransportTest.source_translation_invariance]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticPointIdealNorm.natDegree_norm_of_span_eq_prod #[``IsDedekindDomain.HeightOneSpectrum.quotientEquivPiOfProdEq, ``finrank_quotient_span_eq_natDegree_norm, ``DkMath.Lib.NumberTheory.EllipticPointIdealNorm.finrank_quotient_pointIdeal] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.normDegree_weilNumerator_balance #[``DkMath.Lib.NumberTheory.EllipticPointIdealNorm.natDegree_norm_of_span_eq_prod, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_card, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.span_weilNumerator] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticInfinityValuation.valuationInfty #[``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.degree_norm_add_le, ``Valuation.extendToLocalization] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.infinityOrder_weilFunction #[``DkMath.Lib.NumberTheory.EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.normDegree_weilNumerator] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_eq #[``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_le', ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_le_self', ``Valuation.eq_comap_of_valuationSubring_le_comap_aux] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_placeOf_neg_transEquiv_algebraMap_aux #[``DkMath.Lib.NumberTheory.EllipticInfinityValuation.FunctionField.eq_valuationSubring_of_X_not_mem_aux, ``DkMath.Lib.NumberTheory.EllipticFunctionField.one_lt_valuation_transEquiv_genericX, ``Valuation.eq_of_valuationSubring_eq_aux] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_transEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_transEquiv_eq, ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_placeOf_neg_transEquiv, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_neg_apply] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction_of_torsion #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilFunction] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_weilFunction_pointOrder_transEquiv #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction_of_torsion] false true true false
  checkRoot ``FreyWeilTransportTest.exceptional_translation_pole #[``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_placeOf_neg_transEquiv, ``FreyWeilTransportTest.target_add_self] false true true false
  checkRoot ``FreyWeilTransportTest.normDegree_thirtySeven #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.normDegree_weilNumerator_balance, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_card] false true true false

end Note024DependencyAudit
