/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualDimensionCriteria
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note015DependencyAudit"

/-!
# NOTE-015: 相異なる根・実際の点の正確な計数・直線の外の点の監査

全公開宣言と名前付き回帰宣言の公理を検査する。主要経路は型とopaqueな本体を辿り、
実際の座標同値、無限遠点と有限ファイバーの分離、奇数条件、二倍零点の自己反転を要求する。
指数2の位数4と次元2は三次判別式と実際のファイバーから供給することを検査する。
旧来の位数入力による次元定理、FLT終点、外部未移植宣言、類群providerへの迂回は禁止する。
一般の奇素数に対する根の下界は今回の条件付き判定の外に残る。
-/
namespace Note015DependencyAudit
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
-- Traverse types and opaque bodies of finite fibres, actual elliptic groups and cubic discriminants.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRoots,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.zero_not_mem_affineXFiber,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.mem_divisionRoots_iff,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_killed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_sum_fibers,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_ne_neg_of_odd,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_over_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_eq_two_of_odd,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_prime_sq_of_prime_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_of_prime_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_prime_lt_card,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_exists_outside_span,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_root_count,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_outside_span_iff_root_count,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_eq_one_at_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_two_outside_span,
    ``DkMath.FLT.Frey.Source.residual_odd_card_eq_roots,
    ``DkMath.FLT.Frey.Source.residual_card_eq_prime_sq_of_prime_lt,
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two_iff_prime_lt_card,
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two_iff_exists_outside_span,
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two_iff_root_count,
    ``DkMath.FLT.Frey.Source.residual_exists_outside_span_iff_root_count,
    ``DkMath.FLT.Frey.Source.residual_two_card,
    ``DkMath.FLT.Frey.Source.residual_two_finrank,
    ``DkMath.FLT.Frey.Source.residual_two_exists_outside_span]
  let regression : Array Name := #[
    ``FreyResidualDimensionCriteriaTest.actualCurve2_roots,
    ``FreyResidualDimensionCriteriaTest.actualCurve2_card,
    ``FreyResidualDimensionCriteriaTest.actualCurve2_dimension,
    ``FreyResidualDimensionCriteriaTest.actualTwoPoint_outside_span,
    ``FreyResidualDimensionCriteriaTest.actualCurve37_count,
    ``FreyResidualDimensionCriteriaTest.actualCurve37_frontier,
    ``FreyResidualDimensionCriteriaTest.actualCurve37_outside_frontier,
    ``FreyResidualDimensionCriteriaTest.source37_frontier]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public named NOTE-015 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_sum_fibers #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_coordinate_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_killed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.zero_not_mem_affineXFiber,
    ``Finset.card_biUnion] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_eq_two_of_odd #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_over_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_ne_neg_of_odd,
    ``WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_sum_fibers,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_eq_two_of_odd,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRoots] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_of_prime_lt #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_or_prime_sq,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_exists_outside_span #[
    ``finrank_span_singleton,
    ``Submodule.finrank_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_root_count #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_prime_lt_card] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_two #[
    ``Cubic.card_roots_of_discr_ne_zero,
    ``WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero_of_isElliptic,
    ``WeierstrassCurve.twoTorsionPolynomial_discr] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_two #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_sum_fibers,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_eq_one_at_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_iff_coordinate_root] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_two,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_two #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_two_outside_span #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_exists_outside_span] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_finrank_eq_two_iff_root_count #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_root_count] false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_two_exists_outside_span #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_two_outside_span] false true
  checkRoot ``FreyResidualDimensionCriteriaTest.actualTwoPoint_outside_span #[
    ``FreyResidualRepresentationTest.twoPoint_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_two_outside_span] false true
  checkRoot ``FreyResidualDimensionCriteriaTest.actualCurve37_frontier #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_eq_two_iff_root_count,
    ``FreyResidualRepresentationTest.sample] false true

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_two
#print axioms FreyResidualDimensionCriteriaTest.actualTwoPoint_outside_span

end Note015DependencyAudit
