/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentThreePhase
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenCurrentThreePhaseDependencyAudit"

/-! 同じ六因子の供給、実 receiver の選択根の保存、三項式、係数障害を監査する。
型・opaque を含む本文・構造体のコンストラクタを再帰的に辿る。 -/

namespace SevenCurrentThreePhaseDependencyAudit

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
  logInfo "PASS: required simultaneous-family/selected-root/additive-relation/boundary providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Six complete proof graphs, including opaque bodies and constructors, are checked.
run_cmd do
  let criterion := ``DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion
  let selected := ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver
  let allPhases := ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseIdeal_seventh_power
  let family := ``DkMath.FLT.Kummer.SevenRealGN.exists_current_phase_seventh_family
  checkRoot ``DkMath.Lib.Cosmic.phaseSource_three_consecutive_power_relation #[
    ``DkMath.Lib.Cosmic.phaseSource_three_term_relation,
    ``DkMath.Lib.Cosmic.phaseSource_pow_three_term_relation] #[criterion, selected, allPhases]
  checkRoot family #[
    allPhases,
    ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.normalizedPhaseIdeals_pairwise,
    ``DkMath.FLT.Kummer.SevenRealGN.exists_phase_unit_free_root,
    ``DkMath.FLT.Kummer.SevenRealGN.exists_root_residue_normalizer,
    ``DkMath.FLT.Kummer.SevenRealGN.realPrimary_seventh_of_rotation_fixed,
    criterion] #[selected, ``DkMath.FLT.Kummer.SevenPrimaryNorm.rotate_realGNSource]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.current_three_phase_data_receiver #[
    family,
    ``DkMath.FLT.Kummer.SevenRealGN.currentCarrier_unit_free_factor_receiver,
    ``DkMath.FLT.Kummer.SevenRealGN.current_phase_family_extending_root,
    ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.replaceRoot,
    ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.real_weighted_seventh_equation,
    ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_ideals_pairwise,
    criterion, selected, allPhases]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.real_weighted_seventh_equation #[
    ``DkMath.Lib.Cosmic.phaseSource_three_consecutive_power_relation,
    ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.realGN_factor,
    ``DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ofReal_alpha] #[criterion, selected, allPhases, family]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.no_common_unit_clears_three_phase_coefficients #[
    ``DkMath.FLT.Kummer.SevenRealGN.alphaEmbeddedUnit_not_seventh,
    ``DkMath.FLT.Kummer.SevenRealGN.alphaEmbeddedUnit_normCoordinates] #[criterion, selected, allPhases, family]
  checkRoot ``DkMath.FLT.Kummer.SevenRealGN.CurrentPhaseSeventhFamily.root_not_real #[
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.real_phase_endpoints_unique,
    ``DkMath.FLT.Kummer.SevenRealGN.current_rotation_ne_self] #[criterion, selected, allPhases, family]

end SevenCurrentThreePhaseDependencyAudit
