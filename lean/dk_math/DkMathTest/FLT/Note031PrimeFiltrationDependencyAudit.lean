/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyPrimeFiltrationComplete
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031PrimeFiltrationDependencyAudit"

/-!
# NOTE-031-004 第2部: 還元準同型、乗法的還元、同側輸送の依存監査

型とopaque本体を走査して実際の数学的供給経路を検査する。
標準論理公理以外の公理と外部FLT終点を排除し、一般核にはFLT層への依存も禁止する。
最終APIはabcの可除性、吸収空間、零成分providerを外部入力として要求しない。
-/
namespace Note031PrimeFiltrationDependencyAudit
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
-- 有限の依存グラフ全体を走査する監査コマンドだけ上限を外す。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.ValuationResidue.ne_zero_of_notMem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationResidue.inv_mem_of_notMem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationResidue.coe_mem_nonunits_iff_residue_eq_zero,
    ``DkMath.Lib.NumberTheory.ValuationResidue.div_mem_of_mem_of_notMem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationResidue.residue_ne_zero_of_notMem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationResidue.residue_eq_of_coe_eq,
    ``DkMath.Lib.NumberTheory.ValuationResidue.residue_div,
    ``DkMath.Lib.NumberTheory.ValuationResidue.residue_eq_div_of_eq_div,
    ``DkMath.Lib.NumberTheory.ValuationResidue.residue_eq_residue_iff_sub_mem_nonunits,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.coe_negY,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.negY_mem,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.residue_negY,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.residue_sub_negY,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.residue_inverse_iff,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.slope_mem_residue_of_not_inverse,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.addX_mem_of_not_inverse,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.addY_mem_of_not_inverse,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.residue_addX_of_not_inverse,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.residue_addY_of_not_inverse,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.reducePointSmooth,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.reducePointSmooth_zero,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.reducePointSmooth_some_of_mem,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.reducePointSmooth_some_of_notMem,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.reducePointSmooth_some_of_singular,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.kernel_smooth_and_zero,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.smooth_add_and_reduce,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.smooth_neg,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentSubgroup,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.mem_zeroComponentSubgroup_iff,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentReduction,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.nsmul_reduce_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion,
    ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_torsion_of_model,
    ``DkMath.Lib.NumberTheory.EllipticNodalInertia.smooth_sub_of_model,
    ``DkMath.Lib.NumberTheory.EllipticNodalInertia.critical_pair_smooth_of_model,
    ``DkMath.Lib.NumberTheory.EllipticNodalInertia.inertia_difference_smooth,
    ``DkMath.FLT.Frey.Source.inertia_difference_smooth_at_bad_prime,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_bad_prime,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_p,
    ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p,
    ``DkMath.FLT.Frey.Source.residual_common_side_at_p]
  let regression : Array Name := #[``FreyPrimeFiltrationCompleteTest.nodeModel,
    ``FreyPrimeFiltrationCompleteTest.node_point_nonsingular,
    ``FreyPrimeFiltrationCompleteTest.node_point_reduction_nonsingular,
    ``FreyPrimeFiltrationCompleteTest.node_point_reduction_ne_zero,
    ``FreyPrimeFiltrationCompleteTest.node_point_not_five_torsion,
    ``FreyPrimeFiltrationCompleteTest.source37_bad_absorbs,
    ``FreyPrimeFiltrationCompleteTest.source37_common_side]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticReductionSlope.slope_mem_residue_of_not_inverse #[``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.sub_mul_sub_negY,
    ``DkMath.Lib.NumberTheory.ValuationResidue.residue_eq_div_of_eq_div] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.smooth_add_and_reduce #[``DkMath.Lib.NumberTheory.EllipticReductionKernel.reductionKernel,
    ``DkMath.Lib.NumberTheory.EllipticReductionSlope.residue_addX_of_not_inverse,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.addX_notMem_of_sub_mem_nonunits_of_smooth] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentReduction #[``DkMath.Lib.NumberTheory.EllipticSmoothReduction.smooth_add_and_reduce,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentSubgroup] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.nsmul_reduce_eq_zero #[``DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentReduction,
    ``map_nsmul] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion #[``DkMath.Lib.NumberTheory.EllipticSmoothReduction.nsmul_reduce_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_torsion_of_model #[``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.residue_singular] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalInertia.inertia_difference_smooth #[``DkMath.Lib.NumberTheory.EllipticNodalInertia.smooth_sub_of_model,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model,
    ``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_pair_smooth,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.valuation_apply_eq] true
  checkRoot ``DkMath.FLT.Frey.Source.inertia_difference_smooth_at_bad_prime #[``DkMath.Lib.NumberTheory.EllipticNodalInertia.inertia_difference_smooth,
    ``DkMath.FLT.Frey.Source.exists_criticalCentre_directions_at_bad_prime] false
  checkRoot ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_bad_prime #[``DkMath.FLT.Frey.Source.inertia_difference_smooth_at_bad_prime,
    ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_torsion_of_model,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.charP_residueField] false
  checkRoot ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_p #[``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_bad_prime,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_good_prime] false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p #[``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_p,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_ne_top,
    ``DkMath.Lib.RepresentationTheory.AbsorbingSubspace.fixed_or_cofixed] false
  checkRoot ``DkMath.FLT.Frey.Source.residual_common_side_at_p #[``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy.common_side_on_places] false
  checkRoot ``FreyPrimeFiltrationCompleteTest.node_point_not_five_torsion #[``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentReduction] true
  checkRoot ``FreyPrimeFiltrationCompleteTest.source37_common_side #[``DkMath.FLT.Frey.Source.residual_common_side_at_p] false
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion #[`W, `x₀, `y₀, `he, `hs, `hnode, `P, `hP, `hp] #[`hunit, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalInertia.inertia_difference_smooth #[`E, `A, `M, `hmodel, `C, `D, `σ, `hσ, `hfix, `P] #[`hunit, `htors, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_bad_prime #[`S, `hp2, `hbad, `A, `hA] #[`M, `hM, `habs, `hunit, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_common_side_at_p #[`S, `hp5, `N, `hN, `hbot, `htop] #[`A, `hgood, `hbad, `M, `hM, `habs, `hunit, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentReduction

#print axioms DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_torsion_of_model

#print axioms DkMath.FLT.Frey.Source.residual_common_side_at_p

end Note031PrimeFiltrationDependencyAudit
