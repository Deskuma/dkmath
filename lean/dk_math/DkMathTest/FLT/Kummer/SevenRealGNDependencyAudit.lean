/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealGNConservation
import Lean.Util.FoldConsts

/-! 障害判定・実三次一次合同・反復保存の証明全体を監査する。
七次の整数合同 criterion や既存 FLT 終点から結論を借りない。 -/

open Lean Elab Command
namespace SevenRealGNDependencyAudit

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  #["DkMath.FLT.Kummer.SevenPrimaryNorm.septic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source",
    "DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver"].contains s

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
  logInfo "PASS: required norm/phase/conservation providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Three proof graphs are traversed completely, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.unit_seventh_iff_obstruction #[
    ``DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero,
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.conjugateRatio_finite,
    ``DkMath.Lib.Algebra.oddPower_root_of_square]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_seventh_iff_norm_zero #[
    ``DkMath.FLT.Kummer.SevenRealGN.unit_seventh_iff_obstruction,
    ``DkMath.FLT.Kummer.SevenRealGN.unitRatio_eq_one_of_realPrimary,
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.septic_rootOfUnity_eq_one_of_congruent]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.iterated_invariant_preservation #[
    ``DkMath.FLT.Kummer.SevenRealGN.regauge,
    ``DkMath.Lib.Algebra.root_unit_gauge_identity,
    ``DkMath.Lib.Algebra.dvd_regauged_unit_sub,
    ``DkMath.FLT.Kummer.SevenRealGN.unit_class_preservation,
    ``DkMath.FLT.Kummer.SevenRealGN.root_ideal_preservation]

end SevenRealGNDependencyAudit
