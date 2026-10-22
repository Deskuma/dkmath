/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyBranchComparison
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031BranchComparisonDependencyAudit"

/-!
# NOTE-031-002C5: 実際の和差と鋭い深さ評価の依存監査

型とopaque本体を走査し、既存の中心・方向・滑らかな還元判定と実際の点加法を確認する。
算術の入力を残し、未証明の慣性固定・hcasesや外部FLT解答を経由しない。
-/
namespace Note031BranchComparisonDependencyAudit
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
  let production : Array Name := #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.swapDirections,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.linear_deviation,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.branch_distance_dichotomy,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model,
    ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model,
    ``DkMath.FLT.Frey.Source.shallow_sub_of_same_branch,
    ``DkMath.FLT.Frey.Source.shallow_add_of_opposite_branch]
  let regression : Array Name := #[``FreyBranchComparisonTest.model,
    ``FreyBranchComparisonTest.model_map,
    ``FreyBranchComparisonTest.second_nonsingular,
    ``FreyBranchComparisonTest.secondPoint,
    ``FreyBranchComparisonTest.sum_nonsingular,
    ``FreyBranchComparisonTest.sum_coordinates,
    ``FreyBranchComparisonTest.equal_depth,
    ``FreyBranchComparisonTest.opposite_branches,
    ``FreyBranchComparisonTest.add_comparison,
    ``FreyBranchComparisonTest.sum_integral,
    ``FreyBranchComparisonTest.sharp_depth,
    ``FreyBranchComparisonTest.sub_comparison,
    ``FreyBranchComparisonTest.diagonal_zero,
    ``FreyBranchComparisonTest.inverse_zero]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticBranchComparison.branch_distance_dichotomy #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.linear_deviation,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.slope_mem_and_branches_of_shallow,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff,
    ``WeierstrassCurve.Affine.Point.add_of_X_ne] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.linear_deviation,
    ``DkMath.Lib.NumberTheory.EllipticShallowSlope.negY_branch_distances,
    ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch] true
  checkRoot ``DkMath.FLT.Frey.Source.shallow_sub_of_same_branch #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model,
    ``DkMath.FLT.Frey.Source.valuationModel_map] false
  checkRoot ``DkMath.FLT.Frey.Source.shallow_add_of_opposite_branch #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model,
    ``DkMath.FLT.Frey.Source.valuationModel_map] false
  checkRoot ``FreyBranchComparisonTest.sum_coordinates #[``WeierstrassCurve.Affine.Point.add_of_X_ne,
    ``FreyBranchComparisonTest.second_nonsingular,
    ``FreyBranchComparisonTest.sum_nonsingular] true
  checkRoot ``FreyBranchComparisonTest.add_comparison #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model,
    ``FreyBranchComparisonTest.equal_depth,
    ``FreyBranchComparisonTest.opposite_branches] true
  checkRoot ``FreyBranchComparisonTest.sharp_depth #[``FreyBranchComparisonTest.add_comparison,
    ``FreyBranchComparisonTest.sum_coordinates,
    ``FreyBranchComparisonTest.sum_integral] true
  checkRoot ``FreyBranchComparisonTest.sub_comparison #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model] true
  checkRoot ``FreyBranchComparisonTest.diagonal_zero #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model] true
  checkRoot ``FreyBranchComparisonTest.inverse_zero #[``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model] true
  checkInputs ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch #[`W, `C, `D, `h₁, `h₂, `hX₁, `hX₂, `hlev, `hsh, `hbr] #[`hfix, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model #[`W, `E, `hmodel, `C, `D, `hlev, `hsh, `hbr] #[`hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.shallow_sub_of_same_branch #[`S, `A, `C, `D, `hlev, `hsh, `hbr] #[`hp, `hqp, `hfix, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch #[`W, `C, `D, `h₁, `h₂, `hX₁, `hX₂, `hlev, `hsh, `hbr] #[`hfix, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model #[`W, `E, `hmodel, `C, `D, `hlev, `hsh, `hbr] #[`hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.shallow_add_of_opposite_branch #[`S, `A, `C, `D, `hlev, `hsh, `hbr] #[`hp, `hqp, `hfix, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch

#print axioms DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch

#print axioms DkMath.FLT.Frey.Source.shallow_add_of_opposite_branch

#print axioms FreyBranchComparisonTest.sharp_depth

end Note031BranchComparisonDependencyAudit
