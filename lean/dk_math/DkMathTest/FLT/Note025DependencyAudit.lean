/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilCharacter
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note025DependencyAudit"

/-!
# NOTE-025: 全有限付値から単元を復元し、実際の指標へ着地する経路
新規の名前付き本体・回帰宣言の公理を検査し、選択した型とopaque本体の経路を探索する。
単元のノルム次数、Dedekindの整性判定、同じWeil関数の位数保存、平行移動の合成、
n乗根への着地を要求する。Weil対データ・旧FLT終点・外部未移植providerを禁止する。
-/
namespace Note025DependencyAudit
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
    ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.isUnit_iff_eq_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.exists_eq_algebraMap_of_valuation_eq_one,
    ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_eq_of_pointOrder_eq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.function_scalar_unique,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_of_pointOrder_eq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_const_mul_eigenfunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_weilTranslationUnit,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_spec,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_unique,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnitChar,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_nsmul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_pow,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter_val,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_const_mul_spec,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_const_mul_unique,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator_rescale_div,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_rescaled_numerators,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_zero_target,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_spec,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_pow,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationCharacter,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationCharacter_val]
  let regression : Array Name := #[
    ``FreyWeilCharacterTest.target,
    ``FreyWeilCharacterTest.target_ne_zero,
    ``FreyWeilCharacterTest.coordinate_constant_unit,
    ``FreyWeilCharacterTest.constant_two_valuations,
    ``FreyWeilCharacterTest.recover_constant_two,
    ``FreyWeilCharacterTest.actual_translation_eigenvalue,
    ``FreyWeilCharacterTest.actual_translation_unique,
    ``FreyWeilCharacterTest.actual_translation_square,
    ``FreyWeilCharacterTest.zero_translation,
    ``FreyWeilCharacterTest.actual_translation_multiplicative,
    ``FreyWeilCharacterTest.root_character_square,
    ``FreyWeilCharacterTest.source_character_add,
    ``FreyWeilCharacterTest.scaled_function_eigenvalue,
    ``FreyWeilCharacterTest.zero_target_unit,
    ``FreyWeilCharacterTest.exponent_one,
    ``FreyWeilCharacterTest.exponent_thirtySeven]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.isUnit_iff_eq_algebraMap #[``DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_ne_zero, ``Polynomial.natDegree_eq_zero_of_isUnit] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one #[``IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one, ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.isUnit_iff_eq_algebraMap] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_of_pointOrder_eq #[``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one, ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_surjective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_eq_of_pointOrder_eq, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricCoordinateRing_isDedekindDomain] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_weilTranslationUnit #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_of_pointOrder_eq, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction_of_torsion, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction_ne_zero] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_spec #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_weilTranslationUnit, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add #[``DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_add, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_spec, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.function_scalar_unique] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_pow #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_nsmul, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_zero] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_pow, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add, ``rootsOfUnity, ``AddChar] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_rescaled_numerators #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilNumerator_rescale_div, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_const_mul_unique, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_const_mul_spec] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_weilTranslationCharacter #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter] false true true false
  checkRoot ``FreyWeilCharacterTest.recover_constant_two #[``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one, ``FreyWeilCharacterTest.constant_two_valuations] false true true false
  checkRoot ``FreyWeilCharacterTest.actual_translation_eigenvalue #[``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_spec, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction, ``FreyWeilCharacterTest.target] false true true false
  checkRoot ``FreyWeilCharacterTest.exponent_thirtySeven #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_zero_target, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction_zero] false true true false

end Note025DependencyAudit
