/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyPrimeFiltration
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031PrimeGoodFiltrationDependencyAudit"

/-!
# NOTE-031-004部分実装: 良還元ケース、整点存在、共役輸送と節点捩れの依存監査

型とopaque本体を走査し、実際の供給経路と標準論理公理のみであることを検査する。
p∤abcの仮定を良還元終点の明示入力に保持する。乗法的還元の場合の終点は未供給である。
-/
namespace Note031PrimeGoodFiltrationDependencyAudit
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
  let production : Array Name := #[``DkMath.Lib.RepresentationTheory.AbsorbingSubspace.fixed_or_cofixed,
    ``DkMath.Lib.RepresentationTheory.AbsorbingSubspace.fixed_or_cofixed_of_exists,
    ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.fixedOn_conjugate,
    ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.cofixedOn_conjugate,
    ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.common_side_on_conjugates,
    ``DkMath.Lib.Algebra.SingleSlopeRoot.root_pow_natDegree_mul_leadingCoeff_eq_one,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.addX_mem_of_integral_pole,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.reductionKernel,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.some_mem_iff,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.ofIntegral,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.mem_ofIntegral_iff,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.not_mem_ofIntegral_some,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionKernel.difference_mem_of_congruence,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionKernel.inertia_difference_mem,
    ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.exists_smul_center_eq,
    ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.exists_smul_eq,
    ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.conj_mem_inertia_smul,
    ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.inertia_smul,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy.common_side_on_places,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.Frame,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_some,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.factor_eq,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.not_nonsingular_centre,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.factors_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.eq_zero_of_tc_eq_one,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_neg,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_add,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_nsmul,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.eq_zero_of_prime_smul_eq_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.finite_and_ncard_torsion_le,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.toMap,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.toMap_injective,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion,
    ``DkMath.FLT.Frey.Source.coeff_prePsi_baseChange,
    ``DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line,
    ``DkMath.FLT.Frey.Source.integral_at_valuation,
    ``DkMath.FLT.Frey.Source.residualUnderlyingHom,
    ``DkMath.FLT.Frey.Source.residualReductionKernel,
    ``DkMath.FLT.Frey.Source.mem_residualReductionKernel_iff,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_ne_top,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_good_prime,
    ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p_of_good,
    ``DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good]
  let regression : Array Name := #[``FreyPrimeFiltrationTest.cusp,
    ``FreyPrimeFiltrationTest.pole_nonsingular,
    ``FreyPrimeFiltrationTest.polePoint,
    ``FreyPrimeFiltrationTest.integral_nonsingular,
    ``FreyPrimeFiltrationTest.integralPoint,
    ``FreyPrimeFiltrationTest.cusp_integral,
    ``FreyPrimeFiltrationTest.pole_mem,
    ``FreyPrimeFiltrationTest.double_pole_mem,
    ``FreyPrimeFiltrationTest.integral_plus_pole_x,
    ``FreyPrimeFiltrationTest.sum_nonsingular,
    ``FreyPrimeFiltrationTest.integral_plus_pole,
    ``FreyPrimeFiltrationTest.node5,
    ``FreyPrimeFiltrationTest.node5_no_five_torsion,
    ``FreyPrimeFiltrationTest.source37_good_common_side]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.RepresentationTheory.AbsorbingSubspace.fixed_or_cofixed #[``DkMath.Lib.RepresentationTheory.proper_nonzero_iff_finrank_one,
    ``Submodule.eq_of_le_of_finrank_le] true true
  checkRoot ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.common_side_on_conjugates #[``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.fixedOn_conjugate,
    ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.cofixedOn_conjugate] true true
  checkRoot ``DkMath.Lib.Algebra.SingleSlopeRoot.root_pow_natDegree_mul_leadingCoeff_eq_one #[``Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticReductionKernel.reductionKernel #[``DkMath.Lib.NumberTheory.EllipticReductionKernel.addX_mem_of_integral_pole] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticGoodReductionKernel.inertia_difference_mem #[``DkMath.Lib.NumberTheory.EllipticGoodReductionKernel.difference_mem_of_congruence,
    ``DkMath.Lib.NumberTheory.EllipticReductionKernel.reductionKernel,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits] true false
  checkRoot ``DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line #[``DkMath.Lib.Algebra.SingleSlopeRoot.root_pow_natDegree_mul_leadingCoeff_eq_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_prime_sq,
    ``InfiniteGalois.mem_range_algebraMap_iff_fixed] false false
  checkRoot ``DkMath.FLT.Frey.Source.residualReductionKernel_ne_top #[``DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p_of_good #[``DkMath.FLT.Frey.Source.residualReductionKernel_ne_top,
    ``DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_good_prime,
    ``DkMath.Lib.RepresentationTheory.AbsorbingSubspace.fixed_or_cofixed] false false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.exists_smul_eq #[``DkMath.Lib.NumberTheory.ValuationFrobenius.PlaceTransitivity.le_of_forall_not_mem_nonunits,
    ``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction,
    ``Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite] true false
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy.common_side_on_places #[``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.exists_smul_eq,
    ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.inertia_smul,
    ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.fixedOn_conjugate,
    ``DkMath.Lib.RepresentationTheory.ConjugateLocalConditions.cofixedOn_conjugate] true false
  checkRoot ``DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good #[``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p_of_good,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy.common_side_on_places] false false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion #[``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_add,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.tc_nsmul,
    ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion.eq_zero_of_tc_eq_one] true false
  checkRoot ``FreyPrimeFiltrationTest.double_pole_mem #[``DkMath.Lib.NumberTheory.EllipticReductionKernel.reductionKernel] true false
  checkRoot ``FreyPrimeFiltrationTest.integral_plus_pole #[``WeierstrassCurve.Affine.Point.add_of_X_ne] true false
  checkRoot ``FreyPrimeFiltrationTest.source37_good_common_side #[``DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good] false false
  checkInputs ``DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line #[`S, `hp5, `A, `hA, `N, `hN, `hbot, `htop] #[`hint, `hunit, `hM, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p_of_good #[`S, `hp5, `hgood, `N, `hN, `hbot, `htop, `A, `hA] #[`M, `hM, `habs, `hunit, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good #[`S, `hp5, `hgood, `N, `hN, `hbot, `htop] #[`A, `M, `hM, `habs, `hunit, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion #[`W, `x₀, `y₀, `he, `hs, `hnode, `P, `hP] #[`hunit, `hcases, `hno]

#print axioms DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line

#print axioms DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good

#print axioms DkMath.Lib.NumberTheory.EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion

end Note031PrimeGoodFiltrationDependencyAudit
