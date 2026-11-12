/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualCyclotomic
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note018DependencyAudit"

/-!
# NOTE-018: 条件付き円分行列式と、無条件の円分指標・倍写像全射性の監査

新規公開宣言と回帰例の公理を検査し、指定経路で型とopaque本体を辿る。
行列式の同定には実際のWeilPairingData、その非退化性・同変性と一般の交代対を要求する。
円分指標自体と倍写像の全射性の経路では、対のデータへの依存を逆に禁止する。
対の幾何学的存在providerを得たと誤認しないため、条件付き入口と無条件結果を分けて監査する。
-/
namespace Note018DependencyAudit
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

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) (localOnly : Bool := false) (noPairing : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if (noPairing && ((privateToUserName n).toString.contains "WeilPairingData" ||
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
-- 型とopaque本体を含む有限の依存グラフを全探索するため、通常のタクティク用上限を外す。
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.RepresentationTheory.alternating_skew,
    ``DkMath.Lib.RepresentationTheory.alternating_coordinates,
    ``DkMath.Lib.RepresentationTheory.alternating_basis_ne_zero,
    ``DkMath.Lib.RepresentationTheory.alternating_map_eq_det_smul,
    ``DkMath.Lib.RepresentationTheory.determinantCharacter_eq_of_equivariant_pairing,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.RootSpace,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.rootModule,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.smul_toMul,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.prime_root_card,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec,
    ``DkMath.Lib.NumberTheory.RootPairing,
    ``DkMath.Lib.NumberTheory.RootPairing.zero_left,
    ``DkMath.Lib.NumberTheory.RootPairing.zero_right,
    ``DkMath.Lib.NumberTheory.RootPairing.nsmul_left,
    ``DkMath.Lib.NumberTheory.RootPairing.value_pow,
    ``DkMath.Lib.NumberTheory.RootPairing.rootValue,
    ``DkMath.Lib.NumberTheory.RootPairing.rootValue_eq_zero,
    ``DkMath.Lib.NumberTheory.RootPairing.rootAddHom,
    ``DkMath.Lib.NumberTheory.RootPairing.rootForm,
    ``DkMath.Lib.NumberTheory.RootPairing.rootForm_alternating,
    ``DkMath.Lib.NumberTheory.RootPairing.rootForm_nondegenerate,
    ``DkMath.Lib.NumberTheory.RootPairing.determinant_eq_cyclotomic_of_pairing,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.WeilPairingData,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weil_basis_value_ne_one,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weil_basis_isPrimitiveRoot,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_eq_cyclotomic_of_pairing,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_apply_eq_pow_det_of_pairing,
    ``DkMath.Lib.RepresentationTheory.stable_basis_line_lower_left_zero,
    ``DkMath.Lib.RepresentationTheory.stable_basis_line_diagonal_product,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective,
    ``DkMath.FLT.Frey.Source.ResidualWeilPairingData,
    ``DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic_of_pairing,
    ``DkMath.FLT.Frey.Source.residual_determinant_with_basis_of_pairing,
    ``DkMath.FLT.Frey.Source.residual_apply_eq_pow_det_of_pairing,
    ``DkMath.FLT.Frey.Source.residual_stable_line_diagonal_product_of_pairing,
    ``DkMath.FLT.Frey.Source.residual_curve_multiplication_surjective]
  let regression : Array Name := #[
    ``FreyResidualCyclotomicTest.Plane,
    ``FreyResidualCyclotomicTest.area,
    ``FreyResidualCyclotomicTest.area_alternating,
    ``FreyResidualCyclotomicTest.area_nondegenerate,
    ``FreyResidualCyclotomicTest.diagonalMap,
    ``FreyResidualCyclotomicTest.diagonalRepresentation,
    ``FreyResidualCyclotomicTest.area_equivariant,
    ``FreyResidualCyclotomicTest.diagonal_determinant,
    ``FreyResidualCyclotomicTest.degenerate_pairing_does_not_determine_character,
    ``FreyResidualCyclotomicTest.actual37_cyclotomic_action,
    ``FreyResidualCyclotomicTest.actual37_root_smul,
    ``FreyResidualCyclotomicTest.actual37_multiplication_surjective,
    ``FreyResidualCyclotomicTest.actual4_multiplication_surjective,
    ``FreyResidualCyclotomicTest.zero_multiplication_not_surjective,
    ``FreyResidualCyclotomicTest.actual37_determinant_of_pairing,
    ``FreyResidualCyclotomicTest.actual37_primitive_of_pairing,
    ``FreyResidualCyclotomicTest.source37_determinant_of_pairing]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.RepresentationTheory.alternating_map_eq_det_smul #[
    ``DkMath.Lib.RepresentationTheory.alternating_coordinates,
    ``LinearMap.det_toMatrix] true true true
  checkRoot ``DkMath.Lib.RepresentationTheory.determinantCharacter_eq_of_equivariant_pairing #[
    ``DkMath.Lib.RepresentationTheory.alternating_basis_ne_zero,
    ``DkMath.Lib.RepresentationTheory.alternating_map_eq_det_smul] true true true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter #[
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.prime_root_card,
    ``modularCyclotomicCharacter] true true true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec #[
    ``modularCyclotomicCharacter.spec] true true true
  checkRoot ``DkMath.Lib.NumberTheory.RootPairing.rootForm #[
    ``DkMath.Lib.NumberTheory.RootPairing.value_pow,
    ``AddMonoidHom.toZModLinearMap] true true false
  checkRoot ``DkMath.Lib.NumberTheory.RootPairing.determinant_eq_cyclotomic_of_pairing #[
    ``DkMath.Lib.RepresentationTheory.determinantCharacter_eq_of_equivariant_pairing,
    ``DkMath.Lib.NumberTheory.RootPairing.nondegenerate,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.smul_toMul] true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weil_basis_isPrimitiveRoot #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weil_basis_value_ne_one,
    ``DkMath.Lib.NumberTheory.RootPairing.value_pow,
    ``orderOf_eq_prime] true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_eq_cyclotomic_of_pairing #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.WeilPairingData.equivariant,
    ``DkMath.Lib.NumberTheory.RootPairing.determinant_eq_cyclotomic_of_pairing,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime] true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_apply_eq_pow_det_of_pairing #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_eq_cyclotomic_of_pairing,
    ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec] true true false
  checkRoot ``DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic_of_pairing #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.WeilPairingData,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.WeilPairingData.equivariant,
    ``DkMath.Lib.NumberTheory.RootPairing.nondegenerate,
    ``DkMath.Lib.NumberTheory.RootPairing.rootForm,
    ``DkMath.FLT.Frey.Source.residualBasis] false true false
  checkRoot ``DkMath.FLT.Frey.Source.residual_stable_line_diagonal_product_of_pairing #[
    ``DkMath.FLT.Frey.Source.residual_determinant_with_basis_of_pairing,
    ``DkMath.Lib.RepresentationTheory.stable_basis_line_lower_left_zero] false true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_fiber_natDegree,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_aligned_multiplication_preimage,
    ``IsAlgClosed.exists_root] true true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_curve_multiplication_surjective #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective] false true true
  checkRoot ``FreyResidualCyclotomicTest.diagonal_determinant #[
    ``FreyResidualCyclotomicTest.area_nondegenerate,
    ``FreyResidualCyclotomicTest.area_equivariant,
    ``DkMath.Lib.RepresentationTheory.determinantCharacter_eq_of_equivariant_pairing] false true true
  checkRoot ``FreyResidualCyclotomicTest.degenerate_pairing_does_not_determine_character #[
    ``FreyResidualCyclotomicTest.diagonal_determinant] false true true
  checkRoot ``FreyResidualCyclotomicTest.actual37_determinant_of_pairing #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.WeilPairingData,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_eq_cyclotomic_of_pairing,
    ``FreyResidualRepresentationTest.sample] false true false
  checkRoot ``FreyResidualCyclotomicTest.actual4_multiplication_surjective #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective,
    ``FreyResidualRepresentationTest.sample] false true true
  checkRoot ``FreyResidualCyclotomicTest.zero_multiplication_not_surjective #[
    ``FreyResidualRepresentationTest.twoPoint_ne_zero] false true true

end Note018DependencyAudit
