/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentPrimary
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenCurrentPrimaryDependencyAudit"

/-! 一般の gap 判定、現在の深い gap、実 receiver からの接続を独立に監査する。
整数合同 Kummer criterion と既存 FLT 終点を使わず、現在の receiver は必要な根で必須とする。 -/

namespace SevenCurrentPrimaryDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  #["DkMath.FLT.Kummer.SevenPrimaryNorm.septic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source"].contains s

private def checkRoot (root : Name) (required : Array Name) : CommandElabM Unit := do
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
  for n in required do
    unless visited.contains n do throwError "Required provider absent: {n}"
  logInfo m!"ROOT: {root}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required gap/root-normalization/current-source providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Three complete graphs include opaque proof bodies and inductive constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.exists_primary_root_gauge_iff_gap_divisible #[
    ``DkMath.FLT.Kummer.SevenRealGN.gap_divisible_of_primary,
    ``DkMath.FLT.Kummer.SevenRealGN.exists_root_residue_normalizer,
    ``DkMath.FLT.Kummer.SevenRealGN.seventh_sub_one_dvd_seven_of_residue_one]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.current_gap_seven_phase_dvd #[
    ``DkMath.FLT.Seven.directOrbit_gap_axis_pow32_dvd,
    ``DkMath.FLT.Kummer.SevenRealGN.current_gap_uniformizer_pow64,
    ``DkMath.FLT.Kummer.SevenRealGN.phaseRamifier_dvd_uniformizer]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.currentCarrier_primary_packet_receiver #[
    ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver,
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_eq_realGNSource,
    ``DkMath.FLT.Kummer.SevenRealGN.factor_after_ramifier_twist,
    ``DkMath.FLT.Kummer.SevenRealGN.current_root_away,
    ``DkMath.FLT.Kummer.SevenRealGN.exists_root_residue_normalizer,
    ``DkMath.FLT.Kummer.SevenRealGN.current_gap_seven_phase_dvd,
    ``DkMath.FLT.Kummer.SevenRealGN.primary_of_root_residue_one]

end SevenCurrentPrimaryDependencyAudit
