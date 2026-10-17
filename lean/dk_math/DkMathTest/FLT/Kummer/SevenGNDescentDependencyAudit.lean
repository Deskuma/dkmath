/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenGNDescent
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenGNDescentDependencyAudit"

/-! FLT7終点の実際の底・遷移・GN因子分解・単元補題の来歴を監査する。
型、opaque 本文、構造体のコンストラクタを含む再帰的監査である。 -/

namespace SevenGNDescentDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
  s == "fermatLastTheoremSeven" || s.contains "fermatSeven_no_positive_solution" ||
  s.contains "CurrentCommonPrimeCyclotomicPacket" ||
  s.contains "DirectOrbitSmallerNormPacket" ||
  s == "DkMath.FLT.Kummer.SevenRealGN.currentCorrectionPowerPacket" ||
  s == "DkMath.FLT.Kummer.SevenRealGN.correctionCommonRoot" ||
  s == "DkMath.FLT.Kummer.SevenRealGN.exists_current_phase_seventh_family"

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
  logInfo "PASS: actual GN descent closure providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Traverse two complete proof graphs, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenDescent.fermatLastTheoremFor_seven #[
    ``DkMath.FLT.Kummer.SevenDescent.no_state_one,
    ``DkMath.FLT.Kummer.SevenDescent.descent_step,
    ``DkMath.FLT.Kummer.SevenDescent.initial_state_of_counterexample,
    ``DkMath.FLT.Kummer.SevenDescent.State.exists_weighted_successor,
    ``DkMath.FLT.Kummer.SevenDescent.State.quotient_ideal_power,
    ``DkMath.FLT.Kummer.SevenDescent.ratio_seventh,
    ``DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringIsPrincipalIdealRing,
    ``DkMath.FLT.Seven.CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing,
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion,
    ``DkMath.NumberTheory.GapFocusing.focused_pow_sub_pow_eq_prod_fin,
    ``fermatLastTheoremWith_of_fermatLastTheoremWith_coprime]
  checkRoot ``DkMath.FLT.Kummer.SevenDescent.no_state_one #[
    ``DkMath.FLT.Kummer.SevenDescent.State.distinguished_dvd,
    ``DkMath.FLT.Kummer.SevenDescent.State.product_quotients] #[
    ``DkMath.FLT.Kummer.SevenDescent.descent_step,
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion]
end SevenGNDescentDependencyAudit
