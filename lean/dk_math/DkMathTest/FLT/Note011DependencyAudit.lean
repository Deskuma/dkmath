/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualFiniteLevel
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note011DependencyAudit"

/-!
# NOTE-011: 実際の点・同変同型・有限性の入力を保持する依存監査

全公開宣言の公理を調べ、主要経路では型とopaqueな証明本体も辿る。
外部のFLT終点・正則素数provider・未証明公理に依存しないことに加え、
次元2が濃度公式へ、有限レベルがKrull近傍と開固定部分群へ到達することを要求する。
条件付き定理の引数を証明済みの幾何学的位数公式と読み替える監査ではない。
-/
namespace Note011DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
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
-- Inspect actual types and proof bodies, including the point group law and Krull topology.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.RepresentationTheory.IsStable,
    ``DkMath.Lib.RepresentationTheory.IsIrreducible,
    ``DkMath.Lib.RepresentationTheory.isStable_map_iff,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_of_equivariant,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_iff,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.IsGaloisStable,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.IsIrreducible,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.StandardTorsion,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standardTorsionModule,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv_toAddEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv_val,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standardTorsionAction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standardRepresentation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standardRepresentation_val,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv_equivariant,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionSubmoduleEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_isStable_iff,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_isIrreducible_iff,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_of_card_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_card_sq_iff,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_standard_card_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_eq_iInter,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.FactorsThroughFiniteLevel,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_normal_finite_level,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel,
    ``DkMath.FLT.Frey.Source.IsGaloisStable,
    ``DkMath.FLT.Frey.Source.ResidualIsIrreducible,
    ``DkMath.FLT.Frey.Source.residualStandardEquiv,
    ``DkMath.FLT.Frey.Source.residualStandardEquiv_equivariant,
    ``DkMath.FLT.Frey.Source.residual_standard_isStable_iff,
    ``DkMath.FLT.Frey.Source.residual_standard_isIrreducible_iff,
    ``DkMath.FLT.Frey.Source.residual_isIrreducible_iff,
    ``DkMath.FLT.Frey.Source.residualKernel,
    ``DkMath.FLT.Frey.Source.residualKernel_isOpen,
    ``DkMath.FLT.Frey.Source.ResidualFactorsThroughFiniteLevel,
    ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel,
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two_of_card_sq,
    ``DkMath.FLT.Frey.Source.residual_profile_of_card_sq]
  let regression : Array Name := #[
    ``FreyResidualFiniteLevelTest.standardTwoPoint_ne_zero,
    ``FreyResidualFiniteLevelTest.standardTwoPoint_fixed,
    ``FreyResidualFiniteLevelTest.twoPoint_span_stable,
    ``FreyResidualFiniteLevelTest.twoPoint_span_ne_bot,
    ``FreyResidualFiniteLevelTest.torsionOne_subsingleton,
    ``FreyResidualFiniteLevelTest.torsionOne_not_irreducible,
    ``FreyResidualFiniteLevelTest.torsionOne_finite_level,
    ``FreyResidualFiniteLevelTest.source37_standard_rank,
    ``FreyResidualFiniteLevelTest.source37_profile]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public NOTE-011 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByAddEquiv,
    ``ZMod.map_smul] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standardRepresentation #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction,
    ``WeierstrassCurve.Affine.Point.map] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_isStable_iff #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv_equivariant,
    ``DkMath.Lib.RepresentationTheory.isStable_map_iff] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_isIrreducible_iff #[
    ``DkMath.Lib.RepresentationTheory.isIrreducible_of_equivariant,
    ``DkMath.Lib.RepresentationTheory.isStable_map_iff] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_of_card_sq,
    ``Module.natCard_eq_pow_finrank,
    ``Nat.pow_right_injective] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_eq_iInter #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation,
    ``MulAction.stabilizer] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_stabilizer_isOpen,
    ``krullTopology_mem_nhds_one_iff_of_normal] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_standard_isIrreducible_iff #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_isIrreducible_iff,
    ``DkMath.FLT.Frey.Source.rationalCurve] false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_profile_of_card_sq #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_of_card_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel] false true
  checkRoot ``FreyResidualFiniteLevelTest.standardTwoPoint_fixed #[
    ``DkMath.FLT.Frey.Source.residualStandardEquiv_equivariant,
    ``FreyResidualRepresentationTest.twoPoint_fixed] false true
  checkRoot ``FreyResidualFiniteLevelTest.torsionOne_finite_level #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_one_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel] true true
  checkRoot ``FreyResidualFiniteLevelTest.source37_profile #[
    ``DkMath.FLT.Frey.Source.residual_profile_of_card_sq] false true

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.standard_isIrreducible_iff
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel
#print axioms DkMath.FLT.Frey.Source.residual_profile_of_card_sq

end Note011DependencyAudit
