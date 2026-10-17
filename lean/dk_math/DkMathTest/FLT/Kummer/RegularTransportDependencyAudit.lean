/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.RegularStateTransport
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.RegularTransportDependencyAudit"

/-! Audit every new public declaration, then traverse actual proof graphs including
opaque bodies and constructors. Reject completed FLT endpoints and old sevenfold
base/step proofs, in addition to unexpected axioms. -/

namespace RegularTransportDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
  s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
  s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution" ||
  s == "DkMath.FLT.Kummer.SevenDescent.descent_step" ||
  s == "DkMath.FLT.Kummer.SevenDescent.no_state_one"

private def checkRoot (root : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
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

set_option maxHeartbeats 0 in
-- Traverse all public declarations and seven complete proof graphs, including opaque bodies.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.Cosmic.powerCore,
    ``DkMath.Lib.Cosmic.powerCore_zero_degree,
    ``DkMath.Lib.Cosmic.powerCore_zero_step,
    ``DkMath.Lib.Cosmic.powerCore_zero_base,
    ``DkMath.Lib.Cosmic.pow_add_powerCore,
    ``DkMath.Lib.Cosmic.powerCore_split,
    ``DkMath.Lib.Cosmic.powerCore_swap,
    ``DkMath.Lib.Cosmic.powerCore_split_three,
    ``DkMath.Lib.Cosmic.powerCore_eq_gtail_one,
    ``DkMath.Lib.Cosmic.mul_gtail_one_split,
    ``DkMath.Lib.Cosmic.mul_gtail_one_swap,
    ``DkMath.Lib.Cosmic.powerCore_neg_sum,
    ``DkMath.Lib.Cosmic.odd_sum_eq_mul_gtail_one,
    ``DkMath.Lib.Cosmic.selected_balance_eq_pow_add_powerCore,
    ``DkMath.Lib.Cosmic.powerCore_eq_selected_balance_sub,
    ``DkMath.Lib.Cosmic.selected_nested_transport,
    ``DkMath.Lib.NumberTheory.prime_pow_dvd_scaled_prod_iff,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.slope,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.slope_zero,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.slope_spec,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.slope_residue,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.quotient,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.quotient_spec,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.distinguished,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.quotient_dvd_iff,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.powerCore_eq_product,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.powerCore_dvd_iff,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.sum_dvd_iff,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.gtail_eq_product,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.gap_dvd_iff_of_distinguished_zero,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.not_dvd_gtail_of_distinguished_zero,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.gtail_dvd_iff_of_distinguished_ne_zero,
    ``DkMath.Lib.NumberTheory.cyclotomicRamifiedPhase,
    ``DkMath.Lib.NumberTheory.cyclotomicRamifiedPhase_prime_dvd,
    ``DkMath.FLT.Kummer.RegularDescent.State,
    ``DkMath.FLT.Kummer.RegularDescent.State.uniformizer_dvd_sum,
    ``DkMath.FLT.Kummer.RegularDescent.State.center,
    ``DkMath.FLT.Kummer.RegularDescent.State.center_spec,
    ``DkMath.FLT.Kummer.RegularDescent.State.product_quotients,
    ``DkMath.FLT.Kummer.RegularDescent.State.depth_dvd_iff,
    ``DkMath.FLT.Kummer.RegularDescent.no_state_one,
    ``DkMath.FLT.Kummer.RegularDescent.normalize_weighted,
    ``DkMath.FLT.Kummer.RegularDescent.slope_sub_isUnit,
    ``DkMath.FLT.Kummer.RegularDescent.State.quotient_coprime_y,
    ``DkMath.FLT.Kummer.RegularDescent.State.quotients_coprime,
    ``DkMath.FLT.Kummer.RegularDescent.State.quotient_product,
    ``DkMath.FLT.Kummer.RegularDescent.State.quotient_ideal_power,
    ``DkMath.FLT.Kummer.RegularDescent.State.exists_quotient_roots,
    ``DkMath.FLT.Kummer.RegularDescent.State.exists_descent_roots,
    ``DkMath.FLT.Kummer.RegularDescent.Conditions,
    ``DkMath.FLT.Kummer.RegularDescent.coprime_lambda_of_away,
    ``DkMath.FLT.Kummer.RegularDescent.power_congr_integer,
    ``DkMath.FLT.Kummer.RegularDescent.ratio_congr_power,
    ``DkMath.FLT.Kummer.RegularDescent.ratio_power,
    ``DkMath.FLT.Kummer.RegularDescent.quotient_three_term,
    ``DkMath.FLT.Kummer.RegularDescent.State.exists_weighted_successor,
    ``DkMath.FLT.Kummer.RegularDescent.descent_step,
    ``DkMath.FLT.Kummer.RegularDescent.no_state,
    ``DkMath.FLT.Kummer.RegularDescent.lambda_dvd_intCast_iff,
    ``DkMath.FLT.Kummer.RegularDescent.initial_state_of_int_solution,
    ``DkMath.FLT.Kummer.RegularDescent.not_int_solution_caseII,
    ``DkMath.FLT.Kummer.RegularDescent.cyclotomic_conditions,
    ``DkMath.FLT.Kummer.RegularDescent.no_cubic_state,
    ``DkMath.FLT.Kummer.RegularDescent.no_quintic_state,
    ``DkMath.FLT.Kummer.SevenDescent.regularPhasePacket,
    ``DkMath.FLT.Kummer.SevenDescent.regular_slope_eq,
    ``DkMath.FLT.Kummer.SevenDescent.regular_quotient_eq,
    ``DkMath.FLT.Kummer.SevenDescent.State.toRegular,
    ``DkMath.FLT.Kummer.SevenDescent.ofRegular,
    ``DkMath.FLT.Kummer.SevenDescent.State.regular_distinguished_eq,
    ``DkMath.FLT.Kummer.SevenDescent.State.ramified_depth_dvd_iff,
    ``DkMath.FLT.Kummer.SevenDescent.regularConditions,
    ``DkMath.FLT.Kummer.SevenDescent.descent_step_via_regular,
    ``DkMath.FLT.Kummer.SevenDescent.no_state_via_regular]
  for root in roots do
    let axioms ← liftCoreM <| Lean.collectAxioms root
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} new public declarations use only the allowed logical axioms."
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.descent_step #[
    ``DkMath.FLT.Kummer.RegularDescent.State.exists_weighted_successor,
    ``DkMath.FLT.Kummer.RegularDescent.State.exists_descent_roots,
    ``DkMath.FLT.Kummer.RegularDescent.State.exists_quotient_roots,
    ``DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt,
    ``IsIntegrallyClosed.pow_dvd_pow_iff,
    ``DkMath.Lib.Cosmic.phaseSource_three_term_relation,
    ``DkMath.FLT.Kummer.RegularDescent.ratio_power,
    ``DkMath.FLT.Kummer.RegularDescent.normalize_weighted]
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.no_state #[
    ``DkMath.FLT.Kummer.RegularDescent.no_state_one,
    ``DkMath.FLT.Kummer.RegularDescent.descent_step]
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.no_cubic_state #[
    ``DkMath.FLT.Kummer.cubic_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.cubic_classGroup_card_eq_one]
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.no_quintic_state #[
    ``DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.quintic_classGroup_card_eq_one]
  checkRoot ``DkMath.FLT.Kummer.SevenDescent.descent_step_via_regular #[
    ``DkMath.FLT.Kummer.RegularDescent.descent_step,
    ``DkMath.FLT.Kummer.SevenPrimaryNorm.concrete_kummer_unit_power_criterion]
  checkRoot ``DkMath.FLT.Kummer.SevenDescent.State.ramified_depth_dvd_iff #[
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.sum_dvd_iff]
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.not_int_solution_caseII #[
    ``DkMath.FLT.Kummer.RegularDescent.initial_state_of_int_solution,
    ``DkMath.FLT.Kummer.RegularDescent.no_state]

end RegularTransportDependencyAudit
