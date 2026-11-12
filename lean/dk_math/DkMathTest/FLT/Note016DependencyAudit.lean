/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualRankTwo
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note016DependencyAudit"

/-!
# NOTE-016: 正則ファイバーの根から実際の核への単射と、素数の位数p²の監査

全公開宣言・名前付き回帰の公理を検査し、主要経路で型とopaqueな本体を辿る。
共通根の排除には実際の倍写像とJacobianのX非零性を要求する。下界には有限な例外値、
相異なる根、x座標を保存する単射、平行移動による実際の核との全単射を要求する。
既存の上界へ接続して位数p²と次元2を得る。旧条件付き位数・次元定理、指数2専用の位数、
FLT終点、外部未移植宣言、類群providerへの迂回を禁止する。
これは既約性・行列式・FLTの終点の監査ではない。
-/
namespace Note016DependencyAudit
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
-- Traverse types and opaque bodies of actual points, generic exceptional fibres, embeddings and cardinality.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.wronskian,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.eval_denominator_ne_zero,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.wronskian_ne_zero,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.finite_not_separable_fiber,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.finite_not_squarefree_fiber,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.exists_separable_fiber_avoiding,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_finite_coordinates,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_polynomials_no_common_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_polynomials_isCoprime,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_wronskian_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationFiberPolynomial,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_fiber_natDegree,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.MultiplicationFiber,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionEquivMultiplicationFiber,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_finite_not_separable,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_finite_not_squarefree,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_multiplication_separable_fiber,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_separable_root_card,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_aligned_multiplication_preimage,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRootEmbedding,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_prime_outside_span,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_prime,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_odd_prime,
    ``DkMath.FLT.Frey.Source.residual_card_prime_sq,
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two,
    ``DkMath.FLT.Frey.Source.residual_exists_outside_span,
    ``DkMath.FLT.Frey.Source.residual_rank_two_profile,
    ``DkMath.FLT.Frey.Source.residual_odd_prime_roots]
  let regression : Array Name := #[
    ``FreyResidualRankTwoTest.actualCurve37_card,
    ``FreyResidualRankTwoTest.actualCurve37_dimension,
    ``FreyResidualRankTwoTest.actualCurve37_roots,
    ``FreyResidualRankTwoTest.actualCurve37_outside,
    ``FreyResidualRankTwoTest.actualCurve37_independent_pair,
    ``FreyResidualRankTwoTest.actualCurve4_lower,
    ``FreyResidualRankTwoTest.actualCurve37_standard,
    ``FreyResidualRankTwoTest.source37_profile,
    ``FreyResidualRankTwoTest.quadratic_zero_not_separable]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public named NOTE-016 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.Algebra.RationalPolynomialFiber.wronskian_ne_zero #[
    ``IsCoprime.dvd_of_dvd_mul_right,
    ``Polynomial.natDegree_derivative_lt,
    ``Polynomial.derivative_ne_zero] true true
  checkRoot ``DkMath.Lib.Algebra.RationalPolynomialFiber.finite_not_separable_fiber #[
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.eval_denominator_ne_zero,
    ``Polynomial.finite_setOfPred_isRoot,
    ``Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_finite_coordinates #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.evalEval_ψ_sq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.evalEval_φ,
    ``WeierstrassCurve.Jacobian.Point.toAffineLift_of_Z_ne_zero] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_polynomials_isCoprime #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval,
    ``WeierstrassCurve.Jacobian.X_ne_zero_of_Z_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_affine_equation_y] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_wronskian_ne_zero #[
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.wronskian_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_polynomials_isCoprime,
    ``WeierstrassCurve.natDegree_Φ] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_multiplication_separable_fiber #[
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.finite_not_separable_fiber,
    ``DkMath.Lib.Algebra.RationalPolynomialFiber.exists_separable_fiber_avoiding,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_wronskian_ne_zero] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_separable_root_card #[
    ``Polynomial.nodup_roots,
    ``IsAlgClosed.card_roots_eq_natDegree,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_fiber_natDegree] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRootEmbedding #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_aligned_multiplication_preimage,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_finite_coordinates,
    ``WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff,
    ``WeierstrassCurve.Affine.Point.xRep_neg] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRootEmbedding,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_separable_root_card,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionEquivMultiplicationFiber,
    ``Nat.card_le_card_of_injective] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_le_prime_sq] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq,
    ``Module.natCard_eq_pow_finrank] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.divisionRootCount_odd_prime #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_eq_one_add_twice_roots] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_standardTorsion_prime #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionByLinearEquiv,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_rank_two_profile #[
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime] false true
  checkRoot ``FreyResidualRankTwoTest.actualCurve37_dimension #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime,
    ``FreyResidualRepresentationTest.sample] false true
  checkRoot ``FreyResidualRankTwoTest.actualCurve37_independent_pair #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_nonzero_torsion_of_one_lt,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_torsion_prime_outside_span,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion] false true
  checkRoot ``FreyResidualRankTwoTest.source37_profile #[
    ``DkMath.FLT.Frey.Source.residual_rank_two_profile] false true

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_polynomials_isCoprime
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.square_le_card_torsion
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime
#print axioms FreyResidualRankTwoTest.actualCurve37_independent_pair

end Note016DependencyAudit
