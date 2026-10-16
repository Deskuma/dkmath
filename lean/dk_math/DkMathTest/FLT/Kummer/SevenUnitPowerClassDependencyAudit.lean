/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenUnitPowerClassBridge
import Lean.Util.FoldConsts

/-!
# 同じ source に対する剰余類比較の依存監査

現在の receiver、GN の同じ一次単元、Lib の比較補題を実際に消費することを確認する。
source の同一性は定理の入力であり、監査もその存在を結論しない。
-/

open Lean Elab Command

namespace SevenUnitPowerClassDependencyAudit

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  #["DkMath.FLT.Kummer.cubic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion"].contains s

private def checkRoot (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  let mut bodies : Nat := 0
  let mut axioms : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n then throwError "Forbidden dependency: {n}"
    let some info := env.checked.get.find? n | throwError "Missing constant: {n}"
    pending := pending ++ info.type.getUsedConstants
    if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
    if let .axiomInfo _ := info then
      axioms := axioms.push n
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    match info.value? (allowOpaque := true) with
    | some body =>
      bodies := bodies + 1
      pending := pending ++ body.getUsedConstants
    | none =>
      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => throwError "Unreadable body: {n}"
      | _ => pure ()
  for required in #[
      ``DkMath.Lib.Algebra.quotient_eq_of_fixed_extraction,
      ``DkMath.Lib.Algebra.sameUnitPowerClass_of_fixed_extraction,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GN_primary_unit_seventh,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNRamifierTwist_spec,
      ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver,
      ``NumberField.IsCMField.unitsMulComplexConjInv] do
    unless visited.contains required do throwError "Required provider absent: {required}"
  logInfo m!"ROOT: {root}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required current/GN/class-comparison providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- A complete carrier-to-GN proof graph is traversed, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source

end SevenUnitPowerClassDependencyAudit
