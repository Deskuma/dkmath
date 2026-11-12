/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyTorsionAllCard
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note019DependencyAudit"

/-!
# NOTE-019: 全指数位数公式の依存監査

公開宣言と回帰の公理を検査し、主要経路で型とopaque本体を辿る。
一般可換群の核・商・全射性、実際の倍写像の全射性、既存の素数位数公式と乗法的帰納法を要求する。
全経路でWeil対データ・外部未移植定理・FLT終点・旧条件付き位数providerを禁止する。
一般群の経路は数論層にも依存しないことを検査する。全指数の位数はTate加群の自由性を意味しない。
-/
namespace Note019DependencyAudit
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
    ``DkMath.Lib.Algebra.TorsionMultiplication.Kernel,
    ``DkMath.Lib.Algebra.TorsionMultiplication.inclusion,
    ``DkMath.Lib.Algebra.TorsionMultiplication.multiply,
    ``DkMath.Lib.Algebra.TorsionMultiplication.inclusion_injective,
    ``DkMath.Lib.Algebra.TorsionMultiplication.kernelEquiv,
    ``DkMath.Lib.Algebra.TorsionMultiplication.exact_pair,
    ``DkMath.Lib.Algebra.TorsionMultiplication.multiply_surjective,
    ``DkMath.Lib.Algebra.TorsionMultiplication.short_exact,
    ``DkMath.Lib.Algebra.TorsionMultiplication.quotientEquiv,
    ``DkMath.Lib.Algebra.TorsionMultiplication.card_mul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionInclusion,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionMultiply,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionMultiplyKernelEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_exact_pair,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionInclusion_equivariant,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionMultiply_equivariant,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_short_exact,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_finite_short_exact,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_mul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_one,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_pow,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_standardTorsion_sq,
    ``DkMath.FLT.Frey.Source.curve_torsion_card_sq,
    ``DkMath.FLT.Frey.Source.residual_card_sq,
    ``DkMath.FLT.Frey.Source.curve_torsion_card_mul,
    ``DkMath.FLT.Frey.Source.curve_torsion_pow_card,
    ``DkMath.FLT.Frey.Source.curve_torsion_finite_short_exact,
    ``DkMath.FLT.Frey.Source.curve_torsion_card_finite_level]
  let regression : Array Name := #[
    ``FreyTorsionAllCardTest.actual1_card,
    ``FreyTorsionAllCardTest.actual4_card,
    ``FreyTorsionAllCardTest.actual36_card,
    ``FreyTorsionAllCardTest.actual37square_card,
    ``FreyTorsionAllCardTest.actual37pow_zero,
    ``FreyTorsionAllCardTest.standard4_card,
    ``FreyTorsionAllCardTest.six_six_not_coprime,
    ``FreyTorsionAllCardTest.actual6_6_short_exact,
    ``FreyTorsionAllCardTest.actual6_6_kernel_card,
    ``FreyTorsionAllCardTest.actual6_6_quotient_card,
    ``FreyTorsionAllCardTest.actual1_4_short_exact,
    ``FreyTorsionAllCardTest.zero_factor_exact_pair,
    ``FreyTorsionAllCardTest.actual6_6_inclusion_equivariant,
    ``FreyTorsionAllCardTest.actual6_6_multiply_equivariant,
    ``FreyTorsionAllCardTest.nondivisible_multiply_not_surjective,
    ``FreyTorsionAllCardTest.actual36_card_finite_level,
    ``FreyTorsionAllCardTest.source37_all_card]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.Algebra.TorsionMultiplication.short_exact #[
    ``DkMath.Lib.Algebra.TorsionMultiplication.inclusion_injective,
    ``DkMath.Lib.Algebra.TorsionMultiplication.exact_pair,
    ``DkMath.Lib.Algebra.TorsionMultiplication.multiply_surjective] true true true true
  checkRoot ``DkMath.Lib.Algebra.TorsionMultiplication.card_mul #[
    ``DkMath.Lib.Algebra.TorsionMultiplication.kernelEquiv,
    ``DkMath.Lib.Algebra.TorsionMultiplication.quotientEquiv,
    ``DkMath.Lib.Algebra.TorsionMultiplication.multiply_surjective,
    ``AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup] true true true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_short_exact #[
    ``DkMath.Lib.Algebra.TorsionMultiplication.short_exact,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_finite_short_exact #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_short_exact,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_mul #[
    ``DkMath.Lib.Algebra.TorsionMultiplication.card_mul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq #[
    ``Nat.recOnMul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_mul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_one] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_standardTorsion_sq #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq] true true true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionMultiply_equivariant #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation] true true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_torsion_card_sq #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq] false true true false
  checkRoot ``DkMath.FLT.Frey.Source.curve_torsion_card_finite_level #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero] false true true false
  checkRoot ``FreyTorsionAllCardTest.actual37square_card #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_pow,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq,
    ``FreyResidualRepresentationTest.sample] false true true false
  checkRoot ``FreyTorsionAllCardTest.actual6_6_short_exact #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_finite_short_exact,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective,
    ``FreyResidualRepresentationTest.sample] false true true false
  checkRoot ``FreyTorsionAllCardTest.actual6_6_quotient_card #[
    ``DkMath.Lib.Algebra.TorsionMultiplication.quotientEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective] false true true false
  checkRoot ``FreyTorsionAllCardTest.nondivisible_multiply_not_surjective #[
    ``DkMath.Lib.Algebra.TorsionMultiplication.multiply] false true true true

end Note019DependencyAudit
