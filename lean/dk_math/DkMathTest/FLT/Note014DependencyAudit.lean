/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualNontrivial
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note014DependencyAudit"

/-!
# NOTE-014: 楕円曲線性から非零点・正の次元へ至る証明の監査

全公開宣言と名前付き回帰宣言の公理を検査する。主要経路は型とopaqueな本体まで辿り、
次数の正値性・代数閉包の根・非特異性・実際の倍写像との同値を要求する。
正確な位数や次元2の条件付き定理・FLT終点・類群providerへ迂回しない。
非零点から正の次元へ進む際には、NOTE-012の実際の有限性も辿る。
今回の有限個の経路の監査は、次元1の排除や曲線の分類定理を証明したものではない。
-/
namespace Note014DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || (#[
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_of_card_sq,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_standard_card_sq,
    `DkMath.FLT.Frey.Source.residual_profile_of_card_sq]).contains n || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
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

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) (localOnly : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n || (localOnly && globalProvider (privateToUserName n)) ||
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
-- Traverse types and opaque bodies through the actual elliptic group, root lifting and finite modules.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_affine_equation_y,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_iff_coordinate_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_nontrivial_of_one_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionNontrivial,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_pos,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_bounds,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_one_or_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_or_prime_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_bounds,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_pos,
    ``DkMath.FLT.Frey.Source.residual_exists_ne_zero,
    ``DkMath.FLT.Frey.Source.residual_nontrivial,
    ``DkMath.FLT.Frey.Source.residual_finrank_pos,
    ``DkMath.FLT.Frey.Source.residual_finrank_bounds,
    ``DkMath.FLT.Frey.Source.residual_finrank_one_or_two,
    ``DkMath.FLT.Frey.Source.residual_card_prime_or_prime_sq,
    ``DkMath.FLT.Frey.Source.residual_card_bounds,
    ``DkMath.FLT.Frey.Source.residual_nontrivial_profile]
  let regression : Array Name := #[
    ``FreyResidualNontrivialTest.actualCurve37_exists_ne_zero,
    ``FreyResidualNontrivialTest.actualCurve37_dimension_bounds,
    ``FreyResidualNontrivialTest.actualCurve37_card_bounds,
    ``FreyResidualNontrivialTest.actualCurve37_standard_positive,
    ``FreyResidualNontrivialTest.actualCurve4_exists_ne_zero,
    ``FreyResidualNontrivialTest.source37_profile,
    ``FreyResidualNontrivialTest.cuspidal,
    ``FreyResidualNontrivialTest.cuspidal_origin_equation,
    ``FreyResidualNontrivialTest.cuspidal_origin_singular]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public named NOTE-014 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_affine_equation_y #[
    ``WeierstrassCurve.Affine.monic_polynomial,
    ``Polynomial.Monic.degree_map,
    ``IsAlgClosed.exists_root] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_iff_coordinate_root #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.evalEval_ψ_sq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt #[
    ``WeierstrassCurve.natDegree_ΨSq,
    ``IsAlgClosed.exists_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_affine_equation_y,
    ``WeierstrassCurve.Affine.equation_iff_nonsingular,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_iff_coordinate_root,
    ``WeierstrassCurve.Affine.Point.some_ne_zero] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_pos #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionNontrivial,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``Module.finrank_pos] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_bounds #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_pos,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_or_prime_sq #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_one_or_two,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_pos #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_pos] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_ne_zero #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt] false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_nontrivial_profile #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_pos,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_bounds,
    ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime] false true
  checkRoot ``FreyResidualNontrivialTest.actualCurve37_exists_ne_zero #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt,
    ``FreyResidualRepresentationTest.sample] false true
  checkRoot ``FreyResidualNontrivialTest.actualCurve4_exists_ne_zero #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt,
    ``FreyResidualRepresentationTest.sample] false true
  checkRoot ``FreyResidualNontrivialTest.source37_profile #[
    ``DkMath.FLT.Frey.Source.residual_nontrivial_profile] false true

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_pos
#print axioms DkMath.FLT.Frey.Source.residual_nontrivial_profile

end Note014DependencyAudit
