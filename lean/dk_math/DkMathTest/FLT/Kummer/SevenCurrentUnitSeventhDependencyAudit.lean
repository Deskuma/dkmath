/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentUnitSeventh
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenCurrentUnitSeventhDependencyAudit"

/-! 回転固定性、同じ current 単元の障害消滅、実 receiver、実部分への再入境界を監査する。
整数合同版の concrete criterion は単元橋で必須、座標補題と再入境界では禁止する。 -/

namespace SevenCurrentUnitSeventhDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  s == "DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source"

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
  logInfo "PASS: required rotation/integer-congruence/same-unit/boundary providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Four complete proof graphs, including opaque bodies and constructors, are checked.
run_cmd do
  let criterion := ``DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion
  let receiver := ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver
  checkRoot ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_fixed_mod_seven_integer #[
    ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_fixed_mod_seven_fst,
    ``DkMath.FLT.Seven.SevenRealCubicInt.seven_dvd_iff_coordinates,
    ``DkMath.FLT.Seven.SevenRealCubicInt.rotateEquiv] #[criterion, receiver]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.current_primary_packet_obstruction_zero #[
    ``DkMath.FLT.Seven.SevenRealCubicInt.rotation_fixed_mod_seven_integer,
    ``DkMath.FLT.Seven.directOrbit_gap_axis_pow32_dvd,
    ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_integer_congruence_of_rotation_fixed,
    criterion,
    ``DkMath.FLT.Kummer.SevenRealGN.unit_seventh_iff_obstruction]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.currentCarrier_unit_free_factor_receiver #[
    receiver,
    ``DkMath.FLT.Kummer.SevenRealGN.currentCarrier_primary_packet_receiver,
    ``DkMath.FLT.Kummer.SevenRealGN.current_primary_packet_unit_seventh,
    ``DkMath.FLT.Kummer.SevenRealGN.PrimaryPacket.unit_absorption,
    criterion]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.current_unit_free_root_not_real #[
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.real_phase_endpoints_unique,
    ``DkMath.FLT.Kummer.SevenRealGN.current_rotation_ne_self] #[criterion, receiver]

end SevenCurrentUnitSeventhDependencyAudit
