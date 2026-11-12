/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualGL2
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note017DependencyAudit"

/-!
# NOTE-017: 実際の二次元空間・行列化・安定直線判定の依存監査

公開宣言と回帰例の公理を検査し、指定経路では型とopaqueな証明本体を辿る。
基底には幾何学的な次元定理、行列表示には同じ点への作用、有限レベルには既存の開核、
直線判定には一般の二次元線形代数を要求する。旧条件付き位数provider、外部の未移植宣言、
FLT終点や類群providerへの迂回を禁止する。算術的な既約性や円分指標の同定の監査ではない。
-/
namespace Note017DependencyAudit
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
-- 型とopaque本体を含む有限の依存グラフを全探索するため、通常のタクティク用上限を外す。
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.RepresentationTheory.proper_nonzero_iff_finrank_one,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_iff_no_stable_line,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_val,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_mulVec,
    ``DkMath.Lib.RepresentationTheory.coordinateRepresentation,
    ``DkMath.Lib.RepresentationTheory.coordinate_equivariant,
    ``DkMath.Lib.RepresentationTheory.coordinate_apply_eq_mulVec,
    ``DkMath.Lib.RepresentationTheory.basisChange,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_basis_change,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_ker,
    ``DkMath.Lib.RepresentationTheory.coordinate_isIrreducible_iff,
    ``DkMath.Lib.RepresentationTheory.coordinate_isIrreducible_basis_independent,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_det,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_det_basis_independent,
    ``DkMath.Lib.RepresentationTheory.determinantCharacterWithBasis,
    ``DkMath.Lib.RepresentationTheory.determinantCharacterWithBasis_val,
    ``DkMath.Lib.RepresentationTheory.determinantCharacterWithBasis_independent,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_charpoly,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_charpoly_basis_independent,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionBasis,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2WithBasis,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionCoordinateRepresentation,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2_mulVec,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2_basis_change,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2_ker,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2_kernel_isOpen,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2_normal_finite_level,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_isIrreducible_iff_no_stable_line,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionCoordinate_isIrreducible_iff,
    ``DkMath.FLT.Frey.Source.residualBasis,
    ``DkMath.FLT.Frey.Source.residualGL2WithBasis,
    ``DkMath.FLT.Frey.Source.residualGL2,
    ``DkMath.FLT.Frey.Source.residualCoordinateRepresentation,
    ``DkMath.FLT.Frey.Source.residualGL2_mulVec,
    ``DkMath.FLT.Frey.Source.residualGL2_basis_change,
    ``DkMath.FLT.Frey.Source.residualGL2_ker,
    ``DkMath.FLT.Frey.Source.residualGL2_kernel_isOpen,
    ``DkMath.FLT.Frey.Source.residualGL2_normal_finite_level,
    ``DkMath.FLT.Frey.Source.residual_isIrreducible_iff_no_stable_line,
    ``DkMath.FLT.Frey.Source.residualCoordinate_isIrreducible_iff,
    ``DkMath.FLT.Frey.Source.residualDeterminantCharacter,
    ``DkMath.FLT.Frey.Source.residualDeterminantCharacter_val,
    ``DkMath.FLT.Frey.Source.residual_gl2_profile]
  let regression : Array Name := #[
    ``FreyResidualGL2Test.b37,
    ``FreyResidualGL2Test.swapped37,
    ``FreyResidualGL2Test.swapped37_ne,
    ``FreyResidualGL2Test.actual37_action,
    ``FreyResidualGL2Test.actual37_conjugate,
    ``FreyResidualGL2Test.actual37_determinant,
    ``FreyResidualGL2Test.actual37_charpoly,
    ``FreyResidualGL2Test.actual37_irreducible_basis,
    ``FreyResidualGL2Test.actual37_kernel,
    ``FreyResidualGL2Test.actual37_finite_level,
    ``FreyResidualGL2Test.source37_line_criterion,
    ``FreyResidualGL2Test.actual2_stable_line,
    ``FreyResidualGL2Test.actual2_rank_two_reducible]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.RepresentationTheory.isIrreducible_iff_no_stable_line #[
    ``DkMath.Lib.RepresentationTheory.proper_nonzero_iff_finrank_one,
    ``DkMath.Lib.RepresentationTheory.IsIrreducible,
    ``DkMath.Lib.RepresentationTheory.IsStable] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.matrixGroupHom #[
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom,
    ``Representation.asGroupHom,
    ``LinearMap.toMatrixAlgEquiv] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.matrixGroupHom_basis_change #[
    ``basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,
    ``DkMath.Lib.RepresentationTheory.basisChange] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.matrixGroupHom_ker #[
    ``LinearMap.toMatrixAlgEquiv] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.coordinate_isIrreducible_iff #[
    ``DkMath.Lib.RepresentationTheory.isIrreducible_iff,
    ``DkMath.Lib.RepresentationTheory.coordinate_equivariant] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.determinantCharacterWithBasis_independent #[
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_det,
    ``LinearMap.det_toMatrix] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.matrixGroupHom_charpoly_basis_independent #[
    ``LinearMap.charpoly_toMatrix] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2 #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``Module.finBasisOfFinrankEq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionGL2_normal_finite_level #[
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_ker,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_normal_finite_level] true true
  checkRoot ``DkMath.FLT.Frey.Source.residualGL2 #[
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom] false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_gl2_profile #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_normal_finite_level,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_iff_no_stable_line,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_ker] false true
  checkRoot ``FreyResidualGL2Test.actual37_conjugate #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representation,
    ``DkMath.Lib.RepresentationTheory.matrixGroupHom_basis_change,
    ``FreyResidualRepresentationTest.sample] false true
  checkRoot ``FreyResidualGL2Test.actual2_rank_two_reducible #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``FreyResidualGL2Test.actual2_stable_line,
    ``FreyResidualRepresentationTest.twoPoint_fixed,
    ``DkMath.Lib.RepresentationTheory.isIrreducible_iff_no_stable_line] false true

end Note017DependencyAudit
