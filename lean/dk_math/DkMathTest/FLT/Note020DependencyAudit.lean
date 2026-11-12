/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyTorsionPrimePower
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note020DependencyAudit"

/-!
# NOTE-020: 持ち上げによる生成性・自由性・非分裂性の監査

公開宣言と回帰の公理を検査し、型とopaque本体を辿って指定のproviderを要求する。
自由加群同型には一般群の持ち上げ帰納法・実際の二次元基底・倍写像全射性・全指数位数公式を要求する。
非分裂性には非零基底点の持ち上げとp倍で消える点の性質を要求する。
全ての検査経路でWeil対データ・外部未移植定理・FLT終点等を禁止する。
一般群の生成補題は数論層にも依存しない。Tate加群や互換的基底を証明したとは解釈しない。
-/
namespace Note020DependencyAudit
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
-- 型とopaque本体を含む有限の依存グラフを全探索するため、通常のタクティク用上限を外す。
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.Algebra.TorsionPowerLifting.lifted_pair_generates,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_basis_generates_points,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_power_lifts,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation_surjective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation_bijective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerLifts,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerLifts_spec,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerSuccEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerBasis,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePower_finrank,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerSuccEquiv_symm_apply,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePower_free,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerTransition,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerTransition_surjective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerTransition_equivariant,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerCoordinateRepresentation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerCoordinate_equivariant,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_nsmul_self,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_square_not_killed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_square_order,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_no_additive_section,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_not_product,
    ``DkMath.FLT.Frey.Source.curve_primePowerEquiv,
    ``DkMath.FLT.Frey.Source.curve_primePowerBasis,
    ``DkMath.FLT.Frey.Source.curve_primePower_free,
    ``DkMath.FLT.Frey.Source.curve_primePower_finrank,
    ``DkMath.FLT.Frey.Source.curve_primePower_transition_surjective,
    ``DkMath.FLT.Frey.Source.curve_prime_square_order,
    ``DkMath.FLT.Frey.Source.curve_prime_square_no_section,
    ``DkMath.FLT.Frey.Source.curve_prime_square_not_product]
  let regression : Array Name := #[
    ``FreyTorsionPrimePowerTest.actual37square_equiv,
    ``FreyTorsionPrimePowerTest.actual37cube_free,
    ``FreyTorsionPrimePowerTest.actual37cube_rank,
    ``FreyTorsionPrimePowerTest.actual4_free,
    ``FreyTorsionPrimePowerTest.zero_stage_all_zero,
    ``FreyTorsionPrimePowerTest.zero_stage_equiv,
    ``FreyTorsionPrimePowerTest.actual37square_lifts,
    ``FreyTorsionPrimePowerTest.actual37square_first_coordinate,
    ``FreyTorsionPrimePowerTest.any_lifts_bijective,
    ``FreyTorsionPrimePowerTest.actual37square_transition_surjective,
    ``FreyTorsionPrimePowerTest.actual37square_transition_equivariant,
    ``FreyTorsionPrimePowerTest.actual37square_coordinate_equivariant,
    ``FreyTorsionPrimePowerTest.actual37square_order,
    ``FreyTorsionPrimePowerTest.same_card_not_product,
    ``FreyTorsionPrimePowerTest.actual37square_no_section,
    ``FreyTorsionPrimePowerTest.actual4_not_product]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.Algebra.TorsionPowerLifting.lifted_pair_generates #[] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_basis_generates_points #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionBasis] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_power_lifts #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionBasis] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation_surjective #[``DkMath.Lib.Algebra.TorsionPowerLifting.lifted_pair_generates, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_basis_generates_points] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation_bijective #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation_surjective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq, ``Function.Surjective.bijective_of_nat_card_le] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerSuccEquiv #[``LinearEquiv.ofBijective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerPresentation_bijective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_power_lifts] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePower_free #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerBasis, ``Module.Free.of_basis] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePower_finrank #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerBasis, ``Module.finrank_eq_card_basis] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerTransition_surjective #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerCoordinate_equivariant #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_square_order #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_square_not_killed, ``addOrderOf_eq_prime_pow] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_no_additive_section #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionBasis, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_nsmul_self] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_not_product #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_prime_square_not_killed, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_nsmul_self] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_primePowerEquiv #[``DkMath.FLT.Frey.Source.rationalCurve_isElliptic, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv] false true true false
  checkRoot ``FreyTorsionPrimePowerTest.actual37square_equiv #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerSuccEquiv, ``FreyResidualRepresentationTest.sample] false true true false
  checkRoot ``FreyTorsionPrimePowerTest.actual37square_no_section #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_no_additive_section, ``FreyResidualRepresentationTest.sample] false true true false
  checkRoot ``FreyTorsionPrimePowerTest.same_card_not_product #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_not_product] false true true false

end Note020DependencyAudit
