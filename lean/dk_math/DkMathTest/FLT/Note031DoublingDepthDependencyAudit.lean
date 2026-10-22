/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyDoublingDepth
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031DoublingDepthDependencyAudit"

/-!
# NOTE-031-002C6a: 臨界深さと実際の倍点の依存監査

同じ中心・曲線方程式・実際の点群演算・浅さから分母の非零性を供給する経路を確認する。
相殺閾値を残し、全倍点の軌道・全点の慣性固定を入力として仮定しない。
-/
namespace Note031DoublingDepthDependencyAudit
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
  let production : Array Name := #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.tangentDenominator,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_derivative,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.critical_cubic,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.node_factor_unit,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_separation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_denominator_valuation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_not_two_torsion,
    ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_identity,
    ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_numerator_valuation,
    ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth,
    ``DkMath.FLT.Frey.Source.two_torsion_critical_depth,
    ``DkMath.FLT.Frey.Source.shallow_doubling_depth]
  let regression : Array Name := #[``FreyDoublingDepthTest.family,
    ``FreyDoublingDepthTest.familyCentre,
    ``FreyDoublingDepthTest.threshold_double,
    ``FreyDoublingDepthTest.cancellation_threshold,
    ``FreyDoublingDepthTest.cancellation_strict,
    ``FreyDoublingDepthTest.threshold_rule,
    ``FreyDoublingDepthTest.deeper_point,
    ``FreyDoublingDepthTest.shallower_point,
    ``FreyDoublingDepthTest.deeper_rule,
    ``FreyDoublingDepthTest.shallower_rule,
    ``FreyDoublingDepthTest.bad_point_two_torsion,
    ``FreyDoublingDepthTest.bad_point_critical_depth,
    ``FreyDoublingDepthTest.bad_pair_separated]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_derivative,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.critical_cubic,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.node_factor_unit] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_separation #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.critical_cubic] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_denominator_valuation #[``DkMath.Lib.NumberTheory.EllipticShallowSlope.opposite_slope_separated_of_shallow] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_not_two_torsion #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_denominator_valuation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_derivative] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_identity #[``WeierstrassCurve.Affine.slope_of_Y_ne] true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth #[``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_identity,
    ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_numerator_valuation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_denominator_valuation,
    ``WeierstrassCurve.Affine.Point.add_self_of_Y_ne] true
  checkRoot ``DkMath.FLT.Frey.Source.two_torsion_critical_depth #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth] false
  checkRoot ``DkMath.FLT.Frey.Source.shallow_doubling_depth #[``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth] false
  checkRoot ``FreyDoublingDepthTest.threshold_rule #[``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth,
    ``FreyDoublingDepthTest.cancellation_threshold] true
  checkRoot ``FreyDoublingDepthTest.deeper_rule #[``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth,
    ``FreyDoublingDepthTest.familyCentre,
    ``FreyDoublingDepthTest.deeper_point] true
  checkRoot ``FreyDoublingDepthTest.shallower_rule #[``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth,
    ``FreyDoublingDepthTest.familyCentre,
    ``FreyDoublingDepthTest.shallower_point] true
  checkRoot ``FreyDoublingDepthTest.bad_point_critical_depth #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth,
    ``FreyNodalReductionTest.bad_point_depth] true
  checkRoot ``FreyDoublingDepthTest.bad_pair_separated #[``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_separation,
    ``FreyDoublingDepthTest.bad_point_two_torsion] true
  checkInputs ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth #[`C, `h2, `h, `htor, `hX] #[`hsh, `hfix, `hcases]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_separation #[`C, `h2, `h, `h', `htor, `htor', `hX, `hX', `hne] #[`hfix, `hcases]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_denominator_valuation #[`C, `h, `hX, `hsh] #[`h2, `hΨ, `hfix, `hcases]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_identity #[`C, `h, `hΨ] #[`hfix, `hcases]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth #[`C, `h, `hX, `hsh] #[`hΨ, `htor, `hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.two_torsion_critical_depth #[`S, `A, `C, `h2, `h, `htor, `hX] #[`hfix, `hcases]
  checkInputs ``DkMath.FLT.Frey.Source.shallow_doubling_depth #[`S, `A, `C, `h, `hX, `hsh] #[`hΨ, `htor, `hfix, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth

#print axioms DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth

#print axioms DkMath.FLT.Frey.Source.shallow_doubling_depth

#print axioms FreyDoublingDepthTest.bad_pair_separated

end Note031DoublingDepthDependencyAudit
