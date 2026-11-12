/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyWeilBicharacter
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note026DependencyAudit"

/-!
# NOTE-026: 右加法性・交代性・反対称性の実際の関数体経路
新規本体・回帰の公理と、選択した型・opaque本体の依存を監査する。
倍写像の全射性、既存関数の全点位数、定数比判定、周期的差分、非零積の消去を要求する。
旧FLT終点・外部未移植provider・未構成のWeil対データとその非退化性を借りる経路を禁止する。
-/
namespace Note026DependencyAudit
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
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_mul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_one,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_prod,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_unit_of_pointOrder_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_comp_apply,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_comm_apply,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_range_periodic_difference,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslateOrbitProduct,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslateOrbitProduct_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilTranslateOrbitProduct,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_unit_weilTranslateOrbitProduct,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_weilFunction_self,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_swap,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter_add_right,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter_self,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter_swap,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationRightCharacter,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_apply,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_self,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_swap,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_add_right,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_self,
    ``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_swap,
    ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter,
    ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter_val]
  let regression : Array Name := #[
    ``FreyWeilBicharacterTest.other_coordinates_nonsingular,
    ``FreyWeilBicharacterTest.otherTarget,
    ``FreyWeilBicharacterTest.otherTarget_ne_zero,
    ``FreyWeilBicharacterTest.otherTarget_ne_target,
    ``FreyWeilBicharacterTest.target_double,
    ``FreyWeilBicharacterTest.actualOrbit,
    ``FreyWeilBicharacterTest.actualOrbit_ne_zero,
    ``FreyWeilBicharacterTest.orbit_order_at_infinity,
    ``FreyWeilBicharacterTest.orbit_order_at_finite_point,
    ``FreyWeilBicharacterTest.actualOrbit_is_constant,
    ``FreyWeilBicharacterTest.actual_self_translation,
    ``FreyWeilBicharacterTest.actual_self_unit,
    ``FreyWeilBicharacterTest.other_self_unit,
    ``FreyWeilBicharacterTest.actual_add_right,
    ``FreyWeilBicharacterTest.actual_swap,
    ``FreyWeilBicharacterTest.right_character_add,
    ``FreyWeilBicharacterTest.actual_bicharacter_value,
    ``FreyWeilBicharacterTest.bicharacter_add_left,
    ``FreyWeilBicharacterTest.bicharacter_self,
    ``FreyWeilBicharacterTest.bicharacter_swap,
    ``FreyWeilBicharacterTest.exponent_one,
    ``FreyWeilBicharacterTest.exponent_thirtySeven]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_mul #[``WithZero.log_mul, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_eq_neg_log] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_prod #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_mul] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_of_pointOrder_eq, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_comm_apply, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_unique] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilTranslateOrbitProduct #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_range_periodic_difference, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_prod, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_unit_weilTranslateOrbitProduct #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_unit_of_pointOrder_zero, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilTranslateOrbitProduct, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslateOrbitProduct_ne_zero] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_weilFunction_self #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_unit_weilTranslateOrbitProduct, ``Finset.prod_ne_zero_iff] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_weilFunction_self, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_unique] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_swap #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_self #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter] false true true false
  checkRoot ``FreyWeilBicharacterTest.otherTarget_ne_target #[``FreyWeilBicharacterTest.otherTarget, ``FreyWeilCharacterTest.target] false true true false
  checkRoot ``FreyWeilBicharacterTest.actual_self_unit #[``DkMath.FLT.Frey.Source.curve_weilTranslationUnit_self, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_weilFunction_self] false true true false
  checkRoot ``FreyWeilBicharacterTest.exponent_thirtySeven #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilTranslateOrbitProduct] false true true false

end Note026DependencyAudit
