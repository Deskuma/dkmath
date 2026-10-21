/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilGalois
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note027DependencyAudit"

/-!
# NOTE-027: 半線形作用から同じ固有値への依存監査

全新規宣言の公理と、選択した型・opaque本体の依存を検査する。
座標環の実際の係数作用、分数体への延長、正規化付値、定数比判定、固有値の一意性を要求する。
未構成のWeilPairingData、非退化性のprovider、旧FLT終点や大域Kummer入力を禁止する。
-/
namespace Note027DependencyAudit
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
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRing_polynomial_map,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom_mk,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom_comp,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom_one,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingEquiv_mk,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRing_map_XYIdeal,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_mk,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_algebraMap,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_algebraMap_base,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_genericX,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_genericY,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galAlgHom,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galAlgHom_apply,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_galAlgHom_genericPoint,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_galAlgHom_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_transEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_const_mul,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_one,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_mul,
    ``IsDedekindDomain.HeightOneSpectrum.mem_comap_pow_iff,
    ``IsDedekindDomain.HeightOneSpectrum.intValuation_comap_ringEquiv,
    ``IsDedekindDomain.HeightOneSpectrum.valuation_comap_ringEquiv,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galPoint_xc,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galPoint_yc,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.galPoint_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_galFunctionFieldEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_injective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation_galois,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_inv_cancel,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_galois_weilFunction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galoisUnitMap,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galoisUnitMap_val,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_galois,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galoisRootMap,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galoisRootMap_val,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter_galois,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_galois,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_representation,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_galois,
    ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter_galois,
    ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter_residual]
  let regression : Array Name := #[
    ``FreyWeilGaloisTest.target_fixed,
    ``FreyWeilGaloisTest.other_fixed,
    ``FreyWeilGaloisTest.actual_semilinear,
    ``FreyWeilGaloisTest.generic_x_fixed,
    ``FreyWeilGaloisTest.generic_y_fixed,
    ``FreyWeilGaloisTest.actual_translation,
    ``FreyWeilGaloisTest.actual_finite_valuation,
    ``FreyWeilGaloisTest.actual_generator_scalar,
    ``FreyWeilGaloisTest.actual_unit_galois,
    ``FreyWeilGaloisTest.actual_unit_fixed,
    ``FreyWeilGaloisTest.actual_bicharacter_galois,
    ``FreyWeilGaloisTest.actual_residual_galois,
    ``FreyWeilGaloisTest.exponent_thirtySeven,
    ``FreyWeilGaloisTest.exponent_one]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom, ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom_comp, ``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingHom_one] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.galRingEquiv, ``IsFractionRing.ringEquivOfRingEquiv] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_const_mul #[``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_algebraMap, ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_transEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.map_galAlgHom_genericPoint, ``DkMath.Lib.NumberTheory.EllipticFunctionField.map_galAlgHom_baseChange, ``DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_mk] true true true true
  checkRoot ``IsDedekindDomain.HeightOneSpectrum.valuation_comap_ringEquiv #[``IsDedekindDomain.HeightOneSpectrum.intValuation_comap_ringEquiv, ``IsDedekindDomain.HeightOneSpectrum.mem_comap_pow_iff, ``IsFractionRing.div_surjective] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_galFunctionFieldEquiv #[``DkMath.Lib.NumberTheory.EllipticFunctionField.galRing_map_XYIdeal, ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_asIdeal, ``IsDedekindDomain.HeightOneSpectrum.valuation_comap_ringEquiv] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation_galois #[``DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_galFunctionFieldEquiv, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_galois_weilFunction #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation_galois, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilFunction, ``DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_surjective, ``DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.function_scalar_unique] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_galois #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_galois_weilFunction, ``DkMath.Lib.NumberTheory.EllipticFunctionField.gal_transEquiv, ``DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv_const_mul, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_unique] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_galois #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_galois, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galoisRootMap] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter_residual #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_representation, ``DkMath.FLT.Frey.Source.residualRepresentation, ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic] false true true false
  checkRoot ``FreyWeilGaloisTest.actual_unit_fixed #[``FreyWeilGaloisTest.other_fixed, ``FreyWeilGaloisTest.target_fixed, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_galois] false true true false
  checkRoot ``FreyWeilGaloisTest.exponent_thirtySeven #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_galois, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galoisRootMap] false true true false

end Note027DependencyAudit
