/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyShallowSlope
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031ShallowSlopeDependencyAudit"

/-!
# NOTE-031-002C4: 浅い傾きの整性・排他的な枝・負号の交換を監査する

型とopaque本体を走査し、分離した二根の小さい積、同じ中心の有限Taylor式、
分母の非零性と厳密な浅さを確認する。実際の浅い有理点と2-torsionの境界も監査する。
-/
namespace Note031ShallowSlopeDependencyAudit
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
-- 型とopaque本体を含む有限の依存グラフを全走査する。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.Algebra.ValuationSeparatedRoots.right_eq_one_of_near_left,
    ``DkMath.Lib.Algebra.ValuationSeparatedRoots.left_eq_one_of_near_right,
    ``DkMath.Lib.Algebra.ValuationSeparatedRoots.branches_of_small_product,
    ``DkMath.Lib.Algebra.ValuationSeparatedRoots.not_both_near,
    ``DkMath.Lib.Algebra.ValuationSeparatedRoots.mem_of_small_product,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.shallow_x_ne,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_quadratic,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_factorization,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.branches_of_quadratic_small,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.mem_of_quadratic_small,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_small_of_shallow,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_negY,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.negY_branch_distances,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.opposite_slope_separated_of_shallow,
    ``DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches,
    ``DkMath.FLT.Frey.Source.shallow_opposite_slope_separated]
  let regression : Array Name := #[``FreyShallowSlopeTest.curve,
    ``FreyShallowSlopeTest.curve_invariants,
    ``FreyShallowSlopeTest.defect_at_zero,
    ``FreyShallowSlopeTest.point_nonsingular,
    ``FreyShallowSlopeTest.point,
    ``FreyShallowSlopeTest.point_nonzero_not_two_torsion,
    ``FreyShallowSlopeTest.centre,
    ``FreyShallowSlopeTest.directions,
    ``FreyShallowSlopeTest.point_shallow,
    ``FreyShallowSlopeTest.point_on_second_branch,
    ``FreyShallowSlopeTest.negative_point_on_first_branch,
    ``FreyShallowSlopeTest.old_two_torsion_not_shallow,
    ``FreyShallowSlopeTest.colliding_roots_both_near,
    ``FreyShallowSlopeTest.unit_product_no_near,
    ``FreyShallowSlopeTest.source37_shallow]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.Algebra.ValuationSeparatedRoots.branches_of_small_product #[``DkMath.Lib.Algebra.ValuationSeparatedRoots.right_eq_one_of_near_left,
    ``DkMath.Lib.Algebra.ValuationSeparatedRoots.left_eq_one_of_near_right] true true
  checkRoot ``DkMath.Lib.Algebra.ValuationSeparatedRoots.mem_of_small_product #[``DkMath.Lib.Algebra.ValuationSeparatedRoots.branches_of_small_product] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_quadratic #[``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.translated_equation] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_small_of_shallow #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_quadratic,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.shallow_x_ne] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow #[``DkMath.Lib.Algebra.ValuationSeparatedRoots.mem_of_small_product,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_factorization,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_small_of_shallow,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.branches_of_quadratic_small] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticShallowSlope.negY_branch_distances #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_negY] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticShallowSlope.opposite_slope_separated_of_shallow #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.quadratic_small_of_shallow,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.node_unit,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_negY] true false
  checkRoot ``DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow] false false
  checkRoot ``DkMath.FLT.Frey.Source.shallow_opposite_slope_separated #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.opposite_slope_separated_of_shallow] false false
  checkRoot ``FreyShallowSlopeTest.point_on_second_branch #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow,
    ``FreyShallowSlopeTest.point_shallow,
    ``FreyShallowSlopeTest.point_nonsingular] true false
  checkRoot ``FreyShallowSlopeTest.negative_point_on_first_branch #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.negY_branch_distances,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.opposite_slope_separated_of_shallow,
    ``FreyShallowSlopeTest.point_on_second_branch] true false
  checkRoot ``FreyShallowSlopeTest.old_two_torsion_not_shallow #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.opposite_slope_separated_of_shallow,
    ``FreyNodalReductionTest.bad_point_depth] true false
  checkRoot ``FreyShallowSlopeTest.source37_shallow #[``DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches] false false
  checkInputs ``DkMath.Lib.Algebra.ValuationSeparatedRoots.branches_of_small_product #[`hsep, `hp] #[`ha, `hb, `hfix, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow #[`D, `h, `hnear, `hsh] #[`ht, `hbranch, `hfix, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticShallowSlope.centreSlope_negY #[`C, `x, `y, `hx] #[`hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches #[`S, `A, `D, `h, `hnear, `hsh] #[`hp, `hqp, `ht, `hbranch, `hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.shallow_opposite_slope_separated #[`S, `A, `C, `h, `hnear, `hsh] #[`D, `hfix, `hcases, `hno]

#print axioms DkMath.Lib.Algebra.ValuationSeparatedRoots.branches_of_small_product
#print axioms DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow
#print axioms DkMath.FLT.Frey.Source.shallow_slope_mem_and_branches
#print axioms FreyShallowSlopeTest.point_on_second_branch
#print axioms FreyShallowSlopeTest.old_two_torsion_not_shallow

end Note031ShallowSlopeDependencyAudit
