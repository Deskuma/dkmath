/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreySmoothReductionInertia
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031SmoothReductionDependencyAudit"

/-!
# NOTE-031-002C1: 一点の滑らかさからの実際の慣性固定を監査する

型とopaque本体を走査し、剰余非特異性、差点の極、実際のtorsionの整性と
同じSourceのモデル・一点の滑らかさへ到達することを要求する。
大域固定点排除、旧FLT、外部provider、Kummerへの依存を禁止する。
-/
namespace Note031SmoothReductionDependencyAudit
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
        (algebraOnly && (s.startsWith "NumberField." || s.startsWith "Ideal.inertia" ||
          s.startsWith "Ideal.ramification" ||
          s.startsWith "DkMath.Lib.NumberTheory." ||
          s.startsWith "WeierstrassCurve.")) then
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
  let production : Array Name := #[``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.SmoothCoordinates,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.HasSmoothReduction,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.hasSmoothReduction_zero,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.hasSmoothReduction_some_iff,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.hasSmoothReduction_of_notMem,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.hasSmoothReduction_of_good,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.slope_notMem_of_sub_mem_nonunits_of_smooth,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.addX_notMem_of_sub_mem_nonunits_of_smooth,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence_of_smooth,
    ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction,
    ``DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction]
  let regression : Array Name := #[``FreySmoothReductionInertiaTest.residue_geometry,
    ``FreySmoothReductionInertiaTest.origin_nonsingular,
    ``FreySmoothReductionInertiaTest.smoothTorsion,
    ``FreySmoothReductionInertiaTest.smoothTorsion_ne_zero,
    ``FreySmoothReductionInertiaTest.smoothTorsion_hasSmoothReduction,
    ``FreySmoothReductionInertiaTest.smooth_fixed_at_bad_three,
    ``FreySmoothReductionInertiaTest.singular_coordinates_excluded,
    ``FreySmoothReductionInertiaTest.source37_bad_smooth_fixed]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth #[``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.SmoothCoordinates] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.slope_notMem_of_sub_mem_nonunits_of_smooth #[``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.notMem_nonunits_of_sub_negY_mem_nonunits_of_smooth,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.sub_mul_sub_negY] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence_of_smooth #[``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.addX_notMem_of_sub_mem_nonunits_of_smooth,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_x_mem] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction #[``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence_of_smooth,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits,
    ``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.HasSmoothReduction] true
  checkRoot ``DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction #[``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction,
    ``DkMath.FLT.Frey.Source.valuationModel_map,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd] false
  checkRoot ``FreySmoothReductionInertiaTest.smooth_fixed_at_bad_three #[``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction,
    ``FreySmoothReductionInertiaTest.smoothTorsion_ne_zero,
    ``FreySmoothReductionInertiaTest.smoothTorsion_hasSmoothReduction] true
  checkRoot ``FreySmoothReductionInertiaTest.singular_coordinates_excluded #[``DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.SmoothCoordinates,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.charP_residueField] true
  checkRoot ``FreySmoothReductionInertiaTest.source37_bad_smooth_fixed #[``DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction,
    ``DkMath.FLT.Frey.Source.valuation_c4_eq_one] false
  checkInputs ``DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence_of_smooth #[`hs, `hn, `ht₁, `ht₂, `hxx, `hyy] #[`hgood, `hfix, `hinj, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction #[`hmodel, `hn, `hσ, `P, `hs] #[`hgood, `hfix, `hinj, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction #[`S, `hq, `hqp, `hA, `hσ, `P, `hs] #[`hgood, `hfix, `hinj, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction
#print axioms DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction
#print axioms FreySmoothReductionInertiaTest.smooth_fixed_at_bad_three
#print axioms FreySmoothReductionInertiaTest.singular_coordinates_excluded

end Note031SmoothReductionDependencyAudit
