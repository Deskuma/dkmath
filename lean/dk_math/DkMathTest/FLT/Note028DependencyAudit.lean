/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyGeometricWeilPairing
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note028DependencyAudit"

/-!
# NOTE-028: A・B・Cと実際の対データの依存監査

全新規本体・回帰の公理を検査し、型とopaque本体を含む依存グラフを探索する。
Aの二次反転、Bの忠実な有限群と固定体、Cの局所上界・一重零点・主イデアルを要求する。
幾何学CoreではRootPairingやWeilPairingDataを禁止する。完成後のデータ構成と行列式アダプタでは
それらの実際の構成を必須にし、行列式アダプタのみ既存の基底・位数から次元への補題を許す。
旧FLT終点・未移植provider・大域Kummer入力は全経路で禁止する。
-/
namespace Note028DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) (allowBasis : Bool) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || (!allowBasis && ((#[
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
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two]).contains n)) || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
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

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) (localOnly : Bool := false) (noPairing : Bool := false) (algebraOnly : Bool := false) (allowBasis : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if (algebraOnly && (`DkMath.Lib.NumberTheory.EllipticTorsionRepresentation).isPrefixOf (privateToUserName n)) || (noPairing && ((privateToUserName n).toString.contains "WeilPairingData" ||
        (`DkMath.Lib.NumberTheory.RootPairing).isPrefixOf (privateToUserName n))) || forbidden n allowBasis || (localOnly && globalProvider (privateToUserName n)) ||
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
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.neg_genericPoint_ne_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negHom_injective,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_negPull_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull_comp_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull_comp_pointHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull_comp_negPull,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.coe_negEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negEquiv_apply,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_negEquiv_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negEquiv_genericX,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negEquiv_genericY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.negEquiv_symm,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.coordinateRing_adjoin_X_Y,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.functionField_adjoin_X_Y,
    ``DkMath.Lib.Algebra.QuadraticInvolutionDegree.algHom_ext_of_adjoin_eq_top,
    ``DkMath.Lib.Algebra.QuadraticInvolutionDegree.eq_top_of_forall_mem,
    ``DkMath.Lib.Algebra.QuadraticInvolutionDegree.finrank_fieldRange_le,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.not_forall_nsmul_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.generic_nsmul_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.generic_nsmul_ne_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationHom_injective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationPull,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationPull_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationPull_genericX,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationPull_genericY,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.map_multiplicationPull_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationPull_injective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_multiplicationPull,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.map_negEquiv_nsmul_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.negEquiv_multiplicationPull_genericY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.nsmul_x_formula,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.negEquiv_multiplicationPull_genericY_ne,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finiteDimensional_finrank_multiplicationPull,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionTranslation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionTranslation_injective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionTranslationGroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsionTranslationGroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsionTranslationGroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionFixedField,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsionFixedField,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRange_le_torsionFixedField,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRange_eq_torsionFixedField,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_multiplicationPull,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_multiplicationPull_of_invariant,
    ``DkMath.Lib.Algebra.PullbackPrincipalPrime.le_exp_neg_one_of_lt_one,
    ``DkMath.Lib.Algebra.PullbackPrincipalPrime.isUnit_of_forall_not_mem,
    ``DkMath.Lib.Algebra.PullbackPrincipalPrime.exists_eq_span_of_eq_pullback,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.nsmul_y_formula,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_multiplicationPull_le,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_congr,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.eq_zero_of_invariant_fiber_valuation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_nondegenerate_right,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_right,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_left,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricRootPairing,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricRootPairing_value,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_eq_cyclotomic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_apply_eq_pow_det,
    ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter_nondegenerate,
    ``DkMath.FLT.Frey.Source.residual_geometricWeilPairingData,
    ``DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic,
    ``DkMath.FLT.Frey.Source.residual_apply_eq_pow_det]
  let regression : Array Name := #[
    ``FreyGeometricWeilPairingTest.actual_pull_x,
    ``FreyGeometricWeilPairingTest.actual_pull_y,
    ``FreyGeometricWeilPairingTest.actual_negation_moves_y,
    ``FreyGeometricWeilPairingTest.actual_degree_bound,
    ``FreyGeometricWeilPairingTest.actual_degree,
    ``FreyGeometricWeilPairingTest.degree_thirtySeven,
    ``FreyGeometricWeilPairingTest.actual_translation_group_card,
    ``FreyGeometricWeilPairingTest.actual_fixed_degree,
    ``FreyGeometricWeilPairingTest.actual_fixed_field,
    ``FreyGeometricWeilPairingTest.actual_local_pullback,
    ``FreyGeometricWeilPairingTest.actual_target_detected,
    ``FreyGeometricWeilPairingTest.other_target_detected,
    ``FreyGeometricWeilPairingTest.actual_left_nondegenerate,
    ``FreyGeometricWeilPairingTest.nondegenerate_thirtySeven,
    ``FreyGeometricWeilPairingTest.exponent_one,
    ``FreyGeometricWeilPairingTest.pairing_same_value,
    ``FreyGeometricWeilPairingTest.actualPairing,
    ``FreyGeometricWeilPairingTest.actual_determinant,
    ``FreyGeometricWeilPairingTest.determinant_thirtySeven,
    ``FreyGeometricWeilPairingTest.roots_thirtySeven]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.negEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull, ``DkMath.Lib.NumberTheory.EllipticFunctionField.negPull_comp_negPull, ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_injective_of_ne_baseChange] true true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.functionField_adjoin_X_Y #[``DkMath.Lib.NumberTheory.EllipticFunctionField.coordinateRing_adjoin_X_Y, ``IsFractionRing.div_surjective] true true true true false
  checkRoot ``DkMath.Lib.Algebra.QuadraticInvolutionDegree.finrank_fieldRange_le #[``DkMath.Lib.Algebra.QuadraticInvolutionDegree.algHom_ext_of_adjoin_eq_top, ``IntermediateField.algHomAdjoinIntegralEquiv] true true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.generic_nsmul_ne_zero #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.not_forall_nsmul_eq_zero, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective, ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_transPull_genericPoint] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationPull #[``DkMath.Lib.NumberTheory.EllipticFunctionField.pointPull, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.generic_nsmul_ne_baseChange, ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_injective_of_ne_baseChange] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.negEquiv_multiplicationPull_genericY_ne #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.generic_nsmul_ne_zero, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.map_negEquiv_nsmul_genericPoint] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finiteDimensional_finrank_multiplicationPull #[``DkMath.Lib.Algebra.QuadraticInvolutionDegree.finrank_fieldRange_le, ``DkMath.Lib.NumberTheory.EllipticFunctionField.nsmul_x_formula, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.negEquiv_multiplicationPull_genericY_ne, ``DkMath.Lib.NumberTheory.EllipticFunctionField.functionField_adjoin_X_Y] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsionFixedField #[``FixedPoints.finrank_eq_card, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq, ``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_injective] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRange_eq_torsionFixedField #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finiteDimensional_finrank_multiplicationPull, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_multiplicationPull, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsionFixedField, ``IntermediateField.eq_of_le_of_finrank_le'] true true true false false
  checkRoot ``DkMath.Lib.Algebra.PullbackPrincipalPrime.exists_eq_span_of_eq_pullback #[``IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one, ``IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem] true true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_multiplicationPull_le #[``DkMath.Lib.NumberTheory.EllipticFunctionField.nsmul_y_formula, ``DkMath.Lib.NumberTheory.EllipticFunctionField.nsmul_x_formula, ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_pointPull_le, ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.map_ωe] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.eq_zero_of_invariant_fiber_valuation #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRange_eq_torsionFixedField, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_multiplicationPull_le, ``DkMath.Lib.Algebra.PullbackPrincipalPrime.exists_eq_span_of_eq_pullback, ``WeierstrassCurve.Affine.Point.toClass_eq_zero] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_right #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.eq_zero_of_invariant_fiber_valuation, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilFunction, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_spec] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_left #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_swap, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_right] true true true false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricRootPairing #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_left] true true false false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricRootPairing, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_galois, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_right] true true false false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_eq_cyclotomic #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq, ``DkMath.Lib.NumberTheory.RootPairing.determinant_eq_cyclotomic_of_pairing] true true false false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic #[``DkMath.FLT.Frey.Source.residual_geometricWeilPairingData, ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData] false true false false true
  checkRoot ``FreyGeometricWeilPairingTest.actual_target_detected #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_right, ``FreyWeilCharacterTest.target_ne_zero] false true true false false
  checkRoot ``FreyGeometricWeilPairingTest.degree_thirtySeven #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_multiplicationPull, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finiteDimensional_finrank_multiplicationPull] false true true false false
  checkRoot ``FreyGeometricWeilPairingTest.determinant_thirtySeven #[``DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData] false true false false true

end Note028DependencyAudit
