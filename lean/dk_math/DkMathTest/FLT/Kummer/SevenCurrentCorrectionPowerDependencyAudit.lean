/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentCorrectionPower
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenCurrentCorrectionPowerDependencyAudit"

/-! 固定した F,S の共通七乗因子表示・相対単元・保存パケットの来歴を監査する。
型、opaque 本文、構造体のコンストラクタを含む再帰的監査である。 -/

open Lean Elab Command
namespace SevenCurrentCorrectionPowerDependencyAudit

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  s == "DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source" ||
  s == "DkMath.FLT.Kummer.SevenRealGN.exists_current_phase_seventh_family" ||
  s == "DkMath.FLT.Kummer.SevenRealGN.currentCarrier_unit_free_factor_receiver" ||
  s == "DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver" ||
  s == "DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion"

private def checkRoot (root : Name) (required : Array Name) (extraForbidden : Array Name := #[]) : CommandElabM Unit := do
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
    if forbidden n || extraForbidden.contains n then throwError "Forbidden dependency: {n}"
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
  for n in required do
    unless visited.contains n do throwError "Required provider absent: {n}"
  logInfo m!"ROOT: {root}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required common-quotient/power-split providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Traverse three complete proof graphs, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_factor #[
    ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction,
    ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_smaller_packet,
    ``DkMath.FLT.Seven.DirectOrbitPowerSplitPacket.gap_eq,
    ``DkMath.FLT.Seven.DirectOrbitPowerSplitPacket.gapCore_eq]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.correction_phase_unit_ratio #[] #[
    ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction,
    ``DkMath.FLT.Kummer.SevenRealGN.common_quotient_smaller_packet]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.currentCorrectionPowerPacket #[
    ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_factor,
    ``DkMath.FLT.Kummer.SevenRealGN.correction_common_root_ideal,
    ``DkMath.FLT.Kummer.SevenRealGN.correction_phase_unit_ratio,
    ``DkMath.FLT.Kummer.SevenRealGN.correction_norm_seventh]
end SevenCurrentCorrectionPowerDependencyAudit
