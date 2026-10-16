/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenGNSource
import Lean.Util.FoldConsts

/-!
# GN source 保存と係数環境界の依存監査

正の GN 因子接続と、同じ位相の整数 source への降下を排除する定理を監査する。
単元 criterion・旧 FLT 終点・前章の条件付き source 比較を使わない。
-/

open Lean Elab Command

namespace SevenGNSourceDependencyAudit

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  #["DkMath.FLT.Kummer.cubic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.septic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source",
    "DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver"].contains s

private def checkRoot (root : Name) (boundary : Bool) : CommandElabM Unit := do
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
  let required := if boundary then #[
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.real_phase_eq_integer_GN_iff,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.real_phase_endpoints_unique,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.zeta_pow_im_ne_zero,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.current_rho_not_integer,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNPhaseFactor_eq_realGNSource] else #[
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_eq_realGNSource,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.realGNSource_dvd_GN,
      ``DkMath.NumberTheory.GapFocusing.GN_eq_nontrivial_phase_prod_range]
  for n in required do
    unless visited.contains n do throwError "Required provider absent: {n}"
  logInfo m!"ROOT: {root}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required source/coefficient providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Two complete source proof graphs are traversed, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_dvd_real_GN false
  checkRoot ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_ne_integer_GN_same_phase true

end SevenGNSourceDependencyAudit
