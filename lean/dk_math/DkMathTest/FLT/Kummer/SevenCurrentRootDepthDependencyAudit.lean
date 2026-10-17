/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentRootDepth
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenCurrentRootDepthDependencyAudit"

/-! 与えられた同じ族 F の深い補正項・剰余・局所大域情報と、合同の限界を監査する。
型、opaque 本文、構造体のコンストラクタを含む再帰的監査である。 -/

namespace SevenCurrentRootDepthDependencyAudit

open Lean Elab Command

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
  logInfo "PASS: required gap/common-correction/residue/local-global/norm/congruence/boundary providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Seven complete proof graphs, including opaque bodies and constructors, are checked.
run_cmd do
  let depth := ``DkMath.FLT.Kummer.SevenRealGN.phase_root_seventh_deep
  let gap := ``DkMath.FLT.Kummer.SevenRealGN.current_gap_uniformizer_pow64
  let exactWeighted := ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.real_weighted_seventh_equation
  checkRoot depth #[
    ``DkMath.FLT.Kummer.SevenRealGN.phase_root_gap_identity,
    ``DkMath.FLT.Kummer.SevenRealGN.phaseRootTwist_spec,
    ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction,
    gap] #[exactWeighted]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.phase_root_residue #[
    depth,
    ``ZMod.pow_card,
    ``DkMath.FLT.Kummer.SevenRealGN.ramifiedEval_eq_zero_iff_dvd] #[exactWeighted]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_local_global_data #[
    depth,
    ``DkMath.FLT.Kummer.SevenRealGN.phase_root_residue,
    ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_ideals_pairwise,
    ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseIdeals_pairwise] #[exactWeighted]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.phase_roots_weighted_congruence #[
    depth,
    ``DkMath.FLT.Kummer.SevenRealGN.weighted_common_center_congruence] #[exactWeighted]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction_norm #[
    ``DkMath.FLT.Kummer.SevenRealGN.exists_common_phase_root_correction,
    ``DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.cyclotomicNormHom_ramifiedUniformizer,
    ``Int.natAbs_of_isUnit] #[exactWeighted]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.phase_root_zeta_difference_not_dvd_sq #[
    ``DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ramifiedUniformizer_ne_zero,
    ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_away] #[depth, gap, exactWeighted]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.weighted_common_center_congruence #[]
    #[depth, gap, exactWeighted]

end SevenCurrentRootDepthDependencyAudit
