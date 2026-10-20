/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualDimensionBound
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note013DependencyAudit"

/-!
# NOTE-013: 上界の幾何学的供給と、濃度公式による次元制限の監査

型とopaqueな証明本体を辿り、実際の倍写像・有限性・座標ファイバー・次数上界を要求する。
正確な位数や次元2の条件付き定理、外部のFLT終点や類群providerへの迂回は禁止する。
幾何学だけの部分ではFLT層への逆依存も検査する。全公開宣言と名前付き回帰補題は
標準論理公理だけを許容する。この監査は次元の下界や既約性の証明を代替しない。
-/
namespace Note013DependencyAudit
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
-- Traverse types and opaque proof bodies of the actual elliptic group and all cardinality providers.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_finite,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_le_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_degree_bound,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.degree_bound_lt_cube,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_cases,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_cases,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_le_two,
    ``DkMath.FLT.Frey.Source.residual_card_le_degree_bound,
    ``DkMath.FLT.Frey.Source.residual_finrank_le_two,
    ``DkMath.FLT.Frey.Source.residual_card_le_prime_sq,
    ``DkMath.FLT.Frey.Source.residual_finrank_cases,
    ``DkMath.FLT.Frey.Source.residual_card_prime_cases,
    ``DkMath.FLT.Frey.Source.residual_bounded_profile]
  let regression : Array Name := #[
    ``FreyResidualDimensionBoundTest.actualCurve37_dimension,
    ``FreyResidualDimensionBoundTest.actualCurve37_card,
    ``FreyResidualDimensionBoundTest.actualCurve37_standard_dimension,
    ``FreyResidualDimensionBoundTest.actualCurve2_dimension,
    ``FreyResidualDimensionBoundTest.zero_fiber_singleton,
    ``FreyResidualDimensionBoundTest.source37_profile]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public named NOTE-013 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_le_two #[
    ``WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_degree_bound #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_coordinate_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.affineXFiber_ncard_le_two,
    ``Polynomial.card_roots',
    ``WeierstrassCurve.natDegree_ΨSq_le] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_degree_bound,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.degree_bound_lt_cube,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_cases #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_cases,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_le_two #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_bounded_profile #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq,
    ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime] false true
  checkRoot ``FreyResidualDimensionBoundTest.actualCurve37_card #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq,
    ``FreyResidualRepresentationTest.sample] false true
  checkRoot ``FreyResidualDimensionBoundTest.actualCurve2_dimension #[
    ``DkMath.FLT.Frey.Source.residual_finrank_le_two,
    ``FreyResidualRepresentationTest.twoPoint_ne_zero] false true
  checkRoot ``FreyResidualDimensionBoundTest.zero_fiber_singleton #[
    ``WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff,
    ``FreyResidualRepresentationTest.twoPoint] false true
  checkRoot ``FreyResidualDimensionBoundTest.source37_profile #[
    ``DkMath.FLT.Frey.Source.residual_bounded_profile] false true

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_le_two
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq
#print axioms DkMath.FLT.Frey.Source.residual_bounded_profile

end Note013DependencyAudit
