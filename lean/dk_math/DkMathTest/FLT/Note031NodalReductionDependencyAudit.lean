/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyNodalReduction
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031NodalReductionDependencyAudit"

/-!
# NOTE-031-002C3: 同じ中心の方向と深さの分類を監査する

実際の方向の存在・剰余分離・個別の慣性固定、剰余節点の幾何、滑らかな還元と深さの同値を確認する。
同じSourceの中心・点・モデルの輸送とC1への実際の固定の接続も、型とopaque本体を含めて走査する。
-/
namespace Note031NodalReductionDependencyAudit
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
        (algebraOnly && (s.startsWith "Valuation." || s.startsWith "ValuationSubring." ||
          s.startsWith "DkMath.Lib.NumberTheory.Valuation" ||
          s.startsWith "DkMath.Lib.NumberTheory.EllipticCriticalCentre." ||
          s.startsWith "NumberField." || s.startsWith "Ideal.inertia")) then
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
-- 型とopaque本体を含む有限の依存グラフを全走査する。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.exists_tangentDirections,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.ne,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.difference_square,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.translated_equation,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.roots,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.point_equation,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.residue_ne,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.inertia_fixed,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.nonsingular_of_node_of_x_ne,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_eq_of_singular_of_x_eq,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_small_of_x_small,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_small_of_x_small_of_model,
    ``DkMath.FLT.Frey.Source.exists_criticalCentre_directions_at_bad_prime,
    ``DkMath.FLT.Frey.Source.not_smooth_reduction_iff_depth,
    ``DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre]
  let regression : Array Name := #[``FreyNodalReductionTest.directions_at_three,
    ``FreyNodalReductionTest.exists_nodal_data_at_three,
    ``FreyNodalReductionTest.bad_point_nonsingular,
    ``FreyNodalReductionTest.bad_point_depth,
    ``FreyNodalReductionTest.smooth_point_not_depth,
    ``FreyNodalReductionTest.bad_point_branch_equation,
    ``FreyNodalReductionTest.cuspidal_directions_collide,
    ``FreyNodalReductionTest.source37_directions,
    ``FreyNodalReductionTest.source37_nonclose_fixed]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTangentDirections.exists_tangentDirections #[``IsAlgClosed.exists_eq_mul_self,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.node_unit] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.point_equation #[``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.translated_equation] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.residue_ne #[``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.separated,
    ``IsLocalRing.residue_eq_zero_iff] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.inertia_fixed #[``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_fixed_of_unit_square,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.difference_square] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalReduction.nonsingular_of_node_of_x_ne #[``WeierstrassCurve.c₄] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff #[``DkMath.Lib.NumberTheory.EllipticNodalReduction.nonsingular_of_node_of_x_ne,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_eq_of_singular_of_x_eq,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.residue_singular,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.y_mem_of_x_mem] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_small_of_x_small #[``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_eq_of_singular_of_x_eq] true false
  checkRoot ``DkMath.FLT.Frey.Source.exists_criticalCentre_directions_at_bad_prime #[``DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.exists_tangentDirections,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.inertia_fixed] false false
  checkRoot ``DkMath.FLT.Frey.Source.not_smooth_reduction_iff_depth #[``DkMath.FLT.Frey.Source.valuationModel_map,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre #[``DkMath.FLT.Frey.Source.not_smooth_reduction_iff_depth,
    ``DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction] false false
  checkRoot ``FreyNodalReductionTest.exists_nodal_data_at_three #[``FreyCriticalCentreTest.exists_centre_at_three,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.exists_tangentDirections,
    ``DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.ne] true false
  checkRoot ``FreyNodalReductionTest.bad_point_depth #[``FreySmoothReductionInertiaTest.singular_coordinates_excluded,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.y_small_of_x_small_of_model] true false
  checkRoot ``FreyNodalReductionTest.smooth_point_not_depth #[``FreySmoothReductionInertiaTest.smoothTorsion_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model] true false
  checkRoot ``FreyNodalReductionTest.source37_nonclose_fixed #[``DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre] false false
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTangentDirections.exists_tangentDirections #[`C, `ha₁, `h2] #[`hD, `hfix, `hσv, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff #[`W, `C, `h] #[`h2, `hfix, `hs, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.exists_criticalCentre_directions_at_bad_prime #[`S, `hp, `hq2, `hd, `A, `hA] #[`hD, `hfix, `hσv, `hcases, `hno, `hqp]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre #[`S, `hq, `hqp, `A, `hA, `C, `hσ, `h, `P, `hP, `hdepth] #[`hfix, `hs, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.EllipticTangentDirections.exists_tangentDirections
#print axioms DkMath.Lib.NumberTheory.EllipticTangentDirections.TangentDirections.inertia_fixed
#print axioms DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff
#print axioms DkMath.FLT.Frey.Source.residual_fixed_of_not_close_to_centre
#print axioms FreyNodalReductionTest.bad_point_depth

end Note031NodalReductionDependencyAudit
