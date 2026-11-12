/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyResidualGeometry
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note012DependencyAudit"

/-!
# NOTE-012: 実際の倍写像から有限性・有限レベルまでを辿る監査

新規の名前付き公開宣言と回帰補題の公理を検査し、主要経路では型とopaqueな本体も辿る。
有限性は除法多項式の非零性・座標拘束・有限ファイバーから来ることを要求する。
位数p²からの有限性や次元2、FLT終点、外部の未移植宣言に迂回する経路は禁止する。
標数0と非零次数という定理の明示的な条件を、仮定なしの全標数の結果と読み替えない。
-/
namespace Note012DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || (#[
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_of_card_sq,
    `DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_eq_two_of_card_sq,
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
-- Inspect types and opaque proof bodies through the universal curve and actual elliptic group law.
run_cmd do
  let production : Array Name := #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence',
    ``DkMath.Lib.NumberTheory.EllipticDivision.isEllSequence'_id,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.net,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.net_eq_rel₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.Rel₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.isEllSequence_iff_rel₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.invarNum,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.invarDenom,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.invar_of_net,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.net_add_sub_iff,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_two_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_three_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_even,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_odd,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_same,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_neg₀,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_neg₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_abs₀,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_abs₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_swap,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.StrictAnti₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.avg₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.rel₄_eq_net,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.even_sum,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.avg₄_add_avg₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.same₀₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.abs,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.perm,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.six_le_of_strictAnti₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.addMulSub₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.addMulSub₄_mul_addMulSub₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.addMulSub_transf,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.rel₄_transf,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.transf,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.HaveSameParity₄.strictAnti₄_transf,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₆,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₃_iff₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₆_eq₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₆_eq₃',
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₆_eq₁₀,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_sq_mul_rel₄_eq₉,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.OddRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.EvenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₃_iff_oddRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₃_iff_evenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_iff_evenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.dMin,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.cMin,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.dMin_nonneg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.dMin_lt_cMin,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.negOnePow_cMin_eq_dMin,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.negOnePow_dMin,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.negOnePow_cMin,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.addMulSub_mem_nonZeroDivisors,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.dMin_le,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.Rel₄OfValid,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_fix₁_of_fix₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_of_fix₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_of_min₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_of_anti_oddRec_evenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_abs,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_swap₀₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_swap₁₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_swap₂₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.relFin4,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.relFin4_perm,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.relFin4_perm',
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_same₀₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_same₁₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_same₂₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.rel₄_of_oddRec_evenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.IsEllSequence'.of_oddRec_evenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.map,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.oddRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.evenRec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.zero',
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.sub_add_neg_sub_mul_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.rel₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.net,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.invar,
    ``DkMath.Lib.NumberTheory.EllipticDivision.map_net,
    ``DkMath.Lib.NumberTheory.EllipticDivision.Param,
    ``DkMath.Lib.NumberTheory.EllipticDivision.universalNormEDS,
    ``DkMath.Lib.NumberTheory.EllipticDivision.normEDS_eq_aeval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.normEDS,
    ``DkMath.Lib.NumberTheory.EllipticDivision.IsEllSequence'.ext,
    ``DkMath.Lib.NumberTheory.EllipticDivision.normEDS_two_three_two,
    ``DkMath.Lib.NumberTheory.EllipticDivision.net_normEDS,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Coeff,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective',
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.curve,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Δ_curve_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Poly,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Ring,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Field,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Poly.two_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyToField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyToField_apply,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.algebraMap_field_eq_comp,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.algebraMap_ring_eq_comp,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyToField_polynomial,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.algebraMap_field_injective,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.pointedCurve,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.equation_point,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.point,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.point,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.pointedCurve_a₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.pointedCurve_a₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.pointedCurve_a₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.pointedCurve_a₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.pointedCurve_a₆,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.curvePoly,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.curveRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.curveField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.curveField_eq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.cusp,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.cusp_equation_one_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.specialize,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.map_specialize,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval_apply,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ringEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ringEval_mk,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ringEval_comp_mk,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval_comp_eq_specialize,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ringEval_comp_eq_specialize,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Field.two_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.curveRing_map_ringEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ψc,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.C_Ψ₃_eq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ωe,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.two_mul_ωe,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ωe_spec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ψc_spec,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ωe_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ωe_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ψc_neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.map_ψc,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.map_ωe,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.evalEval_ψ₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.evalEval_Ψ₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.evalEval_preΨ₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.evalEval_ψ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.evalEval_φ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.evalEval_ωe,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.normEDS_rat_two_three_two,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.complEDS₂_rat_two_three_two,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.cusp_ψ₂,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.cusp_Ψ₃,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.cusp_preΨ₄,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval_cusp_ψ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval_cusp_φ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval_cusp_ψc,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyEval_cusp_ωe,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ψᵤ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ψᵤ_eq_normEDS,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.isEllSequence_ψᵤ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.net_ψᵤ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.ψᵤ_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyToField_φ_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.polyToField_ψ₂Sq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_eq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_two,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_sub_smulX,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_sub_sub_smulX_add,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_ne_smulX,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_eq_smulX_iff,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_sub_negY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_one_sub_negY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_one_ne_negY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.slopeOne,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.slopeOne_eq_neg_div,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.addX_smul_one_smul_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.ωe_two_formula,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.addY_smul_one_smul_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.ωe_neg',
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulX_add,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.smulY_add_sub_negY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.zsmul_point_eq_smulX_smulY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.nonsingular_smulX_smulY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.zsmul_point_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.zsmul_point_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.zsmul_point_ne,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.point_point,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulPoly,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.algebraMap_comp_smulRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.zsmul_point_eq_smulField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.dblZ_smulPoly,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.nonsingular_smulField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.dblXYZ_smulField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.dblXYZ_smulRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.addZ_smulPoly,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.ωe_neg_eq_neg_negY,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulPoly_neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulRing_neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulField_neg,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulPoly_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.smulField_zero,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.addXYZ_smulField,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.addXYZ_smulRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.addXYZ_smulField₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.addXYZ_smulRing₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smulEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ringEval_comp_smulRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ringEval_ψ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.dblXYZ_smulEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.addXYZ_smulEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.addXYZ_smulEval₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.evalEval_ψ_sq,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.evalEval_φ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_coordinate_root,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionFinite,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel_of_ne_zero,
    ``DkMath.FLT.Frey.Source.residual_finite_of_ne_zero,
    ``DkMath.FLT.Frey.Source.residualKernel_isOpen_of_prime,
    ``DkMath.FLT.Frey.Source.residual_normal_finite_level,
    ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime]
  let regression : Array Name := #[
    ``FreyResidualGeometryTest.actualCurve37_finite,
    ``FreyResidualGeometryTest.actualCurve37_finite_level,
    ``FreyResidualGeometryTest.twoPoint_coordinate_root,
    ``FreyResidualGeometryTest.source37_finite,
    ``FreyResidualGeometryTest.source37_finite_level]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} public named NOTE-012 declarations and {regression.size} named regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDivision.net_normEDS #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.EllSequence.IsEllSequence'.of_oddRec_evenRec,
    ``normEDS] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ωe #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.ψc,
    ``algebraMap] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.dblXYZ_smulRing,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Jacobian.addXYZ_smulRing₁,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.Univ.Affine.zsmul_point_eq_smulX_smulY] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval,
    ``WeierstrassCurve.Jacobian.Point.toAffineAddEquiv] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_coordinate_root #[
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.evalEval_ψ_sq] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_some_coordinate_root,
    ``WeierstrassCurve.ΨSq_ne_zero,
    ``Polynomial.finite_setOfPred_isRoot,
    ``WeierstrassCurve.Affine.finite_preimage_xRep0] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel_of_ne_zero #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.factorsThroughFiniteLevel,
    ``krullTopology_mem_nhds_one_iff_of_normal] true true
  checkRoot ``DkMath.FLT.Frey.Source.residual_normal_finite_level #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionFinite,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_normal_finite_level] false true
  checkRoot ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointAction_stabilizer_isOpen] false true
  checkRoot ``FreyResidualGeometryTest.actualCurve37_finite_level #[
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``FreyResidualRepresentationTest.sample] false true
  checkRoot ``FreyResidualGeometryTest.twoPoint_coordinate_root #[
    ``FreyResidualRepresentationTest.twoPoint,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ] false true
  checkRoot ``FreyResidualGeometryTest.source37_finite_level #[
    ``DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime] false true

#print axioms DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero
#print axioms DkMath.FLT.Frey.Source.residual_factorsThroughFiniteLevel_of_prime
#print axioms FreyResidualGeometryTest.actualCurve37_finite_level

end Note012DependencyAudit
