/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyUnramifiedAway
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031UnramifiedAwayDependencyAudit"

/-!
# NOTE-031-002: 全点固定までの四状態・整な復帰・有理尺度の依存監査

型とopaque本体の両方を走査し、全倍点の整性、実際の加法、深さの冪の関係、
慣性の正規化合同と鋭いX差を経由して最終定理に達することを確認する。
-/
namespace Note031UnramifiedAwayDependencyAudit
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
  let production : Array Name := #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.chord_of_equal_deviation,
    ``DkMath.Lib.NumberTheory.EllipticAdditionDepth.translated_point,
    ``DkMath.Lib.NumberTheory.EllipticAdditionDepth.same_branch_add,
    ``DkMath.Lib.NumberTheory.EllipticOppositeDepth.opposite_branch_add_of_depth_lt,
    ``DkMath.Lib.NumberTheory.EllipticCriticalAddition.critical_deviations,
    ``DkMath.Lib.NumberTheory.EllipticCriticalAddition.critical_add_shallow,
    ``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_double_not_near,
    ``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_pair_smooth,
    ``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_near,
    ``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_preserves,
    ``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_preserves_of_model,
    ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.smooth_torsion_add_preserves,
    ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth,
    ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth_of_model,
    ``DkMath.Lib.NumberTheory.EllipticDepthInertia.inertia_difference_of_fixed_scale,
    ``DkMath.Lib.NumberTheory.EllipticDepthInertia.torsion_eq_of_strict_depth_difference,
    ``DkMath.Lib.NumberTheory.EllipticDepthInertia.finite_point_fixed_of_rational_depth,
    ``DkMath.FLT.Frey.Source.residual_fixed_at_bad_prime,
    ``DkMath.FLT.Frey.Source.residual_fixed_away_two_self,
    ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self]
  let regression : Array Name := #[``FreyUnramifiedAwayTest.integerCurve,
    ``FreyUnramifiedAwayTest.curve,
    ``FreyUnramifiedAwayTest.model,
    ``FreyUnramifiedAwayTest.model_map,
    ``FreyUnramifiedAwayTest.invariants,
    ``FreyUnramifiedAwayTest.point_nonsingular,
    ``FreyUnramifiedAwayTest.point,
    ``FreyUnramifiedAwayTest.point_three_torsion,
    ``FreyUnramifiedAwayTest.exists_centre_directions,
    ``FreyUnramifiedAwayTest.point_near,
    ``FreyUnramifiedAwayTest.point_depth,
    ``FreyUnramifiedAwayTest.source37_bad_fixed,
    ``FreyUnramifiedAwayTest.source37_fixed,
    ``FreyUnramifiedAwayTest.source37_fixed_cofixed,
    ``FreyUnramifiedAwayTest.smooth_point_nonsingular,
    ``FreyUnramifiedAwayTest.smooth_point_reduction,
    ``FreyUnramifiedAwayTest.return_coordinates,
    ``FreyUnramifiedAwayTest.integral_return_example]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticAdditionDepth.same_branch_add #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow,
    ``WeierstrassCurve.Affine.Point.add_of_X_ne,
    ``WeierstrassCurve.Affine.Point.add_of_Y_ne] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticOppositeDepth.opposite_branch_add_of_depth_lt #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_small_of_shallow,
    ``WeierstrassCurve.Affine.Point.add_of_X_ne] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalAddition.critical_add_shallow #[``DkMath.Lib.NumberTheory.EllipticCriticalAddition.critical_deviations] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_pair_smooth #[``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_double_not_near,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.chord_of_equal_deviation] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_double_not_near #[``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_numerator_valuation] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_near #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_quadratic,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_small_of_x_small] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_preserves #[``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_near,
    ``DkMath.Lib.NumberTheory.EllipticAdditionDepth.same_branch_add,
    ``DkMath.Lib.NumberTheory.EllipticOppositeDepth.opposite_branch_add_of_depth_lt,
    ``DkMath.Lib.NumberTheory.EllipticCriticalAddition.critical_add_shallow] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.smooth_torsion_add_preserves #[``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_preserves,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_x_mem] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth #[``DkMath.Lib.NumberTheory.EllipticTorsionDepth.smooth_torsion_add_preserves,
    ``DkMath.Lib.NumberTheory.EllipticCriticalPair.critical_pair_smooth,
    ``DkMath.Lib.NumberTheory.EllipticAdditionDepth.same_branch_add,
    ``DkMath.Lib.NumberTheory.EllipticOppositeDepth.opposite_branch_add_of_depth_lt,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDepthInertia.inertia_difference_of_fixed_scale #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDepthInertia.torsion_eq_of_strict_depth_difference #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_x_mem] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDepthInertia.finite_point_fixed_of_rational_depth #[``DkMath.Lib.NumberTheory.EllipticDepthInertia.inertia_difference_of_fixed_scale,
    ``DkMath.Lib.NumberTheory.EllipticDepthInertia.torsion_eq_of_strict_depth_difference] true
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_at_bad_prime #[``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth_of_model,
    ``DkMath.Lib.NumberTheory.EllipticDepthInertia.finite_point_fixed_of_rational_depth,
    ``DkMath.FLT.Frey.Source.exists_criticalCentre_directions_at_bad_prime,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction] false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_away_two_self #[``DkMath.FLT.Frey.Source.residual_fixed_at_good_prime,
    ``DkMath.FLT.Frey.Source.residual_fixed_at_bad_prime] false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self #[``DkMath.FLT.Frey.Source.residual_fixed_away_two_self] false
  checkRoot ``FreyUnramifiedAwayTest.point_depth #[``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth_of_model,
    ``FreyUnramifiedAwayTest.point_three_torsion,
    ``FreyUnramifiedAwayTest.point_near] true
  checkRoot ``FreyUnramifiedAwayTest.integral_return_example #[``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_preserves_of_model,
    ``FreyUnramifiedAwayTest.point_depth,
    ``FreyUnramifiedAwayTest.smooth_point_reduction] true
  checkRoot ``FreyUnramifiedAwayTest.source37_fixed #[``DkMath.FLT.Frey.Source.residual_fixed_away_two_self] false
  checkInputs ``DkMath.Lib.NumberTheory.EllipticAdditionDepth.same_branch_add #[`C, `D, `h₁, `h₂, `hX₁, `hX₂, `hsh₁, `hsh₂, `hbr] #[`hcases, `hfix, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticIntegralReturn.integral_smooth_add_near #[`M, `C, `h₁, `h₂, `hP, `hx₁, `hX₂] #[`hsub, `hclosed, `hM, `hfix]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth #[`M, `C, `D, `hodd, `hℓ3, `hunit, `h, `htor, `hX] #[`hsh, `hpow, `hM, `hclosed, `hfix, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticDepthInertia.finite_point_fixed_of_rational_depth #[`E, `n, `A, `M, `hmodel, `hn, `C, `D, `σ, `hσ, `hfix, `h, `ht, `hX, `hsh, `a, `ha, `hdepth] #[`hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_at_bad_prime #[`S, `hp2, `hq, `hq2, `hqp, `hd, `A, `hA, `σ, `hσ, `P] #[`hs, `hsh, `hdepth, `hfix, `hM, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_away_two_self #[`S, `hp2, `hq, `hq2, `hqp, `A, `hA, `σ, `hσ, `P] #[`hd, `hs, `hsh, `hdepth, `hfix, `hM, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self #[`S, `hp2, `hq, `hq2, `hqp, `A, `hA, `N] #[`hs, `hsh, `hfix, `hM, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionDepth.odd_torsion_depth

#print axioms DkMath.FLT.Frey.Source.residual_fixed_away_two_self

#print axioms DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_away_two_self

#print axioms FreyUnramifiedAwayTest.point_depth

end Note031UnramifiedAwayDependencyAudit
