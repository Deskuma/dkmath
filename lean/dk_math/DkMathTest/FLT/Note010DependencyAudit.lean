/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualRepresentation
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note010DependencyAudit"

/-!
# NOTE-010: 実際の点群・Krull連続性・Pascal差分を辿る監査

作用は点の写像から構成し、n倍写像の核を保存することを要求する。
二次元性・局所不分岐性・既約性の供給を混ぜず、FLT終点も禁止する。
試験の非零2-torsion点と、非自明shearの冪の証明も対象に含める。
-/
namespace Note010DependencyAudit
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
-- Traverse types and opaque proof bodies across the elliptic group law, Krull topology and prime binomial proofs.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.Points,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointsAddCommGroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_one,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_mul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGroup,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.Torsion,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.mem_torsionGroup_iff_torsionBy,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByAddEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByAddEquiv_val,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.underlying,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.underlying_killed,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_one_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.underlying_injective,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionModule,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionAction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.underlying_representation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_inverse,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGaloisAction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.galois_smul_def,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.baseChangePoint,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_baseChange,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_stabilizer_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionTopology,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionDiscreteTopology,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_stabilizer_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionContinuousSMul,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation_orbit_continuous,
    ``DkMath.Lib.RepresentationTheory.PascalDifference.polynomial_difference_pow,
    ``DkMath.Lib.RepresentationTheory.PascalDifference.end_difference_pow,
    ``DkMath.Lib.RepresentationTheory.PascalDifference.representation_difference_pow,
    ``DkMath.Lib.RepresentationTheory.PascalDifference.difference_pow_eq_zero_of_image_pow,
    ``DkMath.Lib.RepresentationTheory.PascalDifference.difference_pow_eq_zero_of_pow_eq_one,
    ``DkMath.FLT.Frey.Source.ResidualSpace,
    ``DkMath.FLT.Frey.Source.residualRepresentation,
    ``DkMath.FLT.Frey.Source.residualAutomorphisms,
    ``DkMath.FLT.Frey.Source.residualAutomorphisms_coe,
    ``DkMath.FLT.Frey.Source.residual_underlying,
    ``DkMath.FLT.Frey.Source.residual_action_continuous,
    ``DkMath.FLT.Frey.Source.residual_difference_pow,
    ``DkMath.FLT.Frey.Source.residual_difference_nilpotent,
    ``DkMath.FLT.Frey.Source.ofCounterexample_residual_entrance]
  let regression : Array Name := #[
    ``FreyResidualRepresentationTest.sample,
    ``FreyResidualRepresentationTest.zero_coordinates_nonsingular,
    ``FreyResidualRepresentationTest.twoPoint,
    ``FreyResidualRepresentationTest.twoPoint_ne_zero,
    ``FreyResidualRepresentationTest.twoPoint_fixed,
    ``FreyResidualRepresentationTest.Plane,
    ``FreyResidualRepresentationTest.shift,
    ``FreyResidualRepresentationTest.shift_square,
    ``FreyResidualRepresentationTest.shear,
    ``FreyResidualRepresentationTest.shear_difference,
    ``FreyResidualRepresentationTest.shear_pow,
    ``FreyResidualRepresentationTest.shear_ne_one]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public NOTE-010 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGroup,
    ``nsmulAddMonoidHom,
    ``WeierstrassCurve.Affine.Point.map,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionModule] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByAddEquiv #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.mem_torsionGroup_iff_torsionBy,
    ``Submodule.torsionBy] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_stabilizer_isOpen #[
    ``stabilizer_isOpen_of_isIntegral,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionContinuousSMul #[
    ``continuousSMul_iff_stabilizer_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_stabilizer_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.PascalDifference.end_difference_pow #[
    ``DkMath.Lib.RepresentationTheory.PascalDifference.polynomial_difference_pow,
    ``sub_pow_char,
    ``Polynomial.aeval,
    ``Nat.Prime.dvd_choose_pow] true true
  checkRoot ``DkMath.FLT.Frey.Source.residualRepresentation #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation,
    ``DkMath.FLT.Frey.Source.rationalCurve] false true
  checkRoot ``DkMath.FLT.Frey.Source.residualAutomorphisms #[
    ``Representation.asGroupHom,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation] false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_difference_nilpotent #[
    ``DkMath.Lib.RepresentationTheory.PascalDifference.difference_pow_eq_zero_of_image_pow,
    ``DkMath.FLT.Frey.Source.residualRepresentation] false true
  checkRoot ``DkMath.FLT.Frey.Source.ofCounterexample_residual_entrance #[
    ``DkMath.FLT.Frey.Source.ofCounterexample,
    ``DkMath.FLT.Frey.exists_primitiveReduction,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionContinuousSMul,
    ``DkMath.FLT.Frey.Source.ofCounterexample_local_profile] false true
  checkRoot ``FreyResidualRepresentationTest.twoPoint #[
    ``WeierstrassCurve.Affine.Point.add_self_of_Y_eq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGroup,
    ``FreyResidualRepresentationTest.zero_coordinates_nonsingular] false true
  checkRoot ``FreyResidualRepresentationTest.shear_pow #[
    ``DkMath.Lib.RepresentationTheory.PascalDifference.end_difference_pow,
    ``FreyResidualRepresentationTest.shift_square] true true

#print axioms DkMath.FLT.Frey.Source.residualRepresentation
#print axioms DkMath.FLT.Frey.Source.residual_action_continuous
#print axioms DkMath.FLT.Frey.Source.ofCounterexample_residual_entrance
#print axioms DkMath.Lib.RepresentationTheory.PascalDifference.end_difference_pow

end Note010DependencyAudit
