/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyDyadicInertia
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031DyadicInertiaDependencyAudit"

/-!
# NOTE-031-003: Frobenius・野生合同・実点固定・直線と商の依存監査

型とopaque本体を走査し、論理公理の制限と実際の証明経路を確認する。
終点がFrobeniusや野生固定を入力に取っていないことも束縛名で検査する。
-/
namespace Note031DyadicInertiaDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx ||
    s.startsWith "DkMath.Lib.NumberTheory.RegularKummer." ||
    s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit." || s.startsWith "FltRegular." || s.startsWith "P2M." ||
    s.startsWith "P2MW." || s.startsWith "FreyPackage." ||
    s.contains "fermatLastTheorem" || s.contains "fermat_last_theorem" ||
    s.contains "fermatThree_no_positive_solution" ||
    (`DkMath.FLT.Kummer).isPrefixOf (privateToUserName n)

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false)
    (algebraOnly : Bool := false) (withoutFolded : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let s := (privateToUserName n).toString
    if forbidden n || (neutral && s.startsWith "DkMath.FLT.") ||
        (withoutFolded && s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit.") ||
        (algebraOnly && (s.startsWith "WeierstrassCurve." ||
          s.startsWith "DkMath.Lib.NumberTheory." || s.startsWith "NumberField." ||
          s.startsWith "Ideal.inertia")) then
      throwError "Forbidden dependency: {n}"
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

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input missing in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; explicit arithmetic guards and remaining inputs retained."

set_option maxHeartbeats 0 in
-- 型とopaque本体を含む有限の依存グラフを全走査するため、監査コマンドだけ上限を外す。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.RepresentationTheory.ConjugateSquare.eq_id_on_line_of_conj_eq_sq,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.IsFrobeniusAt,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.IsFrobeniusAt.mem_decompositionSubgroup,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.IsFrobeniusAt.smul_residue_eq,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.Zbar,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.coe_mem,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.toPlace,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.coe_toPlace,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.center,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.mem_center_iff,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.center_isPrime,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.center_under,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.mem_smul_nonunits_iff,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.le_of_forall_not_mem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.isGalois_Qbar,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.isAlgebraic_Qbar,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.smul_eq_of_smul_center_eq,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.exists_frobenius_algEquiv,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_iff,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_mem_iff,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_mem_nonunits_iff,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.mem_decompositionSubgroup_of_forall,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_sub_self_mem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_of_forall,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.conj_mem_inertiaSubgroupIn,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.mul_mem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.valuation_lt_of_lt,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.exists_pow_apply_eq,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.not_valuation_apply_lt,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.valuation_apply_eq,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_mul_inv_mem,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq_of_mem,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq_eq_rq_iff,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq_mul,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq_one,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq_apply_mul_inv_eq_one,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.rq_apply_eq_pow_of_isFrobeniusAt,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_ne_zero,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_shift,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_mul,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_pow,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_mul_theta_inv,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_frob_conj,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.exists_conjugate_pow_wild,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.lt_mul_self,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.one_lt_mul_self,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.mul_lt_mul_right_pos,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.lt_of_mul_lt_mul_right_pos,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.le_of_mul_le_mul_right_pos,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.a₁,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.a₂,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.a₃,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.a₄,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.a₆,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_y_le_one,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_pole,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_addX_of_slope,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_three,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_addX_double,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.addX_T0,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.PoleOrZero,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_zero,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_some_iff,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_double,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_add_T0,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.model,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.Integral.model_map,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.torsion_x_mem,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.eq_zero_of_poleOrZero,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_a₄_le_of_torsion,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_two_y_add_x,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_sub_of_unit,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_ratio_le_one,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_sub_of_node,
    ``DkMath.Lib.NumberTheory.EllipticDyadicWildInertia.fixed_of_wild,
    ``DkMath.FLT.Frey.Source.residual_order_unit_at_two,
    ``DkMath.FLT.Frey.Source.residual_fixed_of_dyadic_wild,
    ``DkMath.FLT.Frey.Source.residual_exists_dyadic_conjugate_square,
    ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two]
  let regression : Array Name := #[``FreyDyadicInertiaTest.shear,
    ``FreyDyadicInertiaTest.diagonal,
    ``FreyDyadicInertiaTest.line,
    ``FreyDyadicInertiaTest.shear_fixed_cofixed,
    ``FreyDyadicInertiaTest.shear_not_identity,
    ``FreyDyadicInertiaTest.source37_fixed_cofixed]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.RepresentationTheory.ConjugateSquare.eq_id_on_line_of_conj_eq_sq #[``Submodule.finrank_quotient_add_finrank,
    ``LinearMap.surjective_of_injective] true true
  checkRoot ``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime #[``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction,
    ``Ideal.Quotient.stabilizerHom_surjective_of_profinite,
    ``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.exists_frobenius_algEquiv] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationTameCharacter.exists_conjugate_pow_wild #[``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_frob_conj,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.theta_pow] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_a₄_le_of_torsion #[``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_double,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_add_T0,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_x_mem] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDyadicWildInertia.fixed_of_wild #[``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.v_a₄_le_of_torsion,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_sub_of_node,
    ``DkMath.Lib.NumberTheory.EllipticDyadicSeparation.poleOrZero_sub_of_unit] true false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_of_dyadic_wild #[``DkMath.Lib.NumberTheory.EllipticDyadicWildInertia.fixed_of_wild,
    ``DkMath.FLT.Frey.Source.valuationModel_map] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_dyadic_conjugate_square #[``DkMath.FLT.Frey.Source.residual_fixed_of_dyadic_wild,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.exists_conjugate_pow_wild] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two #[``DkMath.FLT.Frey.Source.residual_exists_dyadic_conjugate_square,
    ``DkMath.FLT.Frey.Source.residual_finrank_eq_two,
    ``DkMath.Lib.RepresentationTheory.ConjugateSquare.eq_id_on_line_of_conj_eq_sq] false false
  checkRoot ``FreyDyadicInertiaTest.shear_fixed_cofixed #[``DkMath.Lib.RepresentationTheory.ConjugateSquare.eq_id_on_line_of_conj_eq_sq] true false
  checkRoot ``FreyDyadicInertiaTest.source37_fixed_cofixed #[``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two] false false
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two #[`S, `hp2, `N, `hN, `hbot, `htop, `A, `hA] #[`hcases, `hno, `hφ, `hwild, `h2, `hfix, `hrel]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_dyadic_conjugate_square #[`S, `hp2, `A, `hA] #[`φ, `hφ, `hwild, `hcases, `hrel]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime #[`hq, `A, `hA] #[`φ, `hφ, `hrel]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationTameCharacter.exists_conjugate_pow_wild #[`hq, `A, `hA] #[`φ, `hφ, `hrel]

#print axioms DkMath.Lib.RepresentationTheory.ConjugateSquare.eq_id_on_line_of_conj_eq_sq

#print axioms DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime

#print axioms DkMath.FLT.Frey.Source.residual_fixed_of_dyadic_wild

#print axioms DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two

end Note031DyadicInertiaDependencyAudit
