/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.PhaseRigidityFLT
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.PhaseRigidityFLTDependencyAudit"

/-!
Check all new named declarations and actual transitive proof graphs, including opaque
bodies, types and constructors. Structural FLT normalization/equivalence lemmas and
our new endpoints and their generated proof auxiliaries are allowed by exact parent names; any other completed FLT is rejected.
-/

namespace PhaseRigidityFLTDependencyAudit

open Lean Elab Command

private def allowedFLT : Array Name := #[
  ``fermatLastTheoremWith_of_fermatLastTheoremWith_coprime,
  ``fermatLastTheoremFor_iff_int,
  ``fermatLastTheoremWith_nat_int_rat_tfae,
  ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_of_regular_prime,
  ``DkMath.FLT.Kummer.fermatLastTheoremFor_of_regular_prime,
  ``DkMath.FLT.Kummer.fermatLastTheoremFor_eleven,
  ``DkMath.FLT.Kummer.fermatLastTheoremFor_thirteen,
  ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_eleven,
  ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_thirteen]

private def forbidden (n : Name) : Bool :=
  let userName := privateToUserName n
  let s := userName.toString
  userName == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
  (s.contains "fermatLastTheorem" && !allowedFLT.contains userName &&
    !allowedFLT.any (fun root => root.isPrefixOf userName)) ||
  s.contains "fermatThree_no_positive_solution" ||
  s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  s == "DkMath.FLT.Kummer.SevenDescent.descent_step" ||
  s == "DkMath.FLT.Kummer.SevenDescent.no_state_one"

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n || (neutral && (privateToUserName n).toString.startsWith "DkMath.FLT.") then throwError "Forbidden dependency: {n}"
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
-- The finite audit traverses 36 declarations and four large transitive proof graphs.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.dvd_phase_coefficients_of_zero,
    ``DkMath.Lib.NumberTheory.dvd_phase_coefficient_sub,
    ``DkMath.Lib.NumberTheory.phase_sum_dvd_iff,
    ``DkMath.Lib.NumberTheory.phase_coefficients_modEq,
    ``DkMath.Lib.NumberTheory.dvd_phase_coefficients_of_support_lt,
    ``DkMath.Lib.NumberTheory.fourPhaseCoeff,
    ``DkMath.Lib.NumberTheory.sum_fourPhaseCoeff,
    ``DkMath.Lib.NumberTheory.exists_fourPhaseCoeff_eq_zero,
    ``DkMath.Lib.NumberTheory.four_phase_obstruction,
    ``DkMath.Lib.NumberTheory.RegularKummer.eq_one_mod_one_sub,
    ``DkMath.Lib.NumberTheory.RegularKummer.complexConj_zeta,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_inv_conj_not_neg_zeta_runity_aux,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_inv_conj_not_neg_zeta_runity,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_inv_conj_is_root_of_unity,
    ``DkMath.FLT.Kummer.CaseIConjugation.pow_sub_intGalConj_mem,
    ``DkMath.FLT.Kummer.CaseIConjugation.exists_int_sum_eq_zero'_aux,
    ``DkMath.FLT.Kummer.CaseIConjugation.exists_int_sum_eq_zero',
    ``DkMath.FLT.Kummer.CaseIConjugation.exists_int_sum_eq_zero,
    ``DkMath.FLT.Kummer.CaseIConjugation.Packet,
    ``DkMath.FLT.Kummer.CaseIConjugation.exists_adjacent_phases,
    ``DkMath.FLT.Kummer.CaseIConjugation.packet_of_factor,
    ``DkMath.FLT.Kummer.coprime_right_of_flt_equation,
    ``DkMath.FLT.Kummer.prime_dvd_right_of_two_congruences,
    ``DkMath.FLT.Kummer.orient_first_case,
    ``DkMath.FLT.Kummer.orient_second_case,
    ``DkMath.FLT.Kummer.positive_state_of_second_case,
    ``DkMath.FLT.Kummer.first_case_conjugation_packet,
    ``DkMath.FLT.Kummer.not_int_solution_caseI_of_not_modEq,
    ``DkMath.FLT.Kummer.not_int_solution_caseI,
    ``DkMath.FLT.Kummer.not_int_solution_regular_prime,
    ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_of_regular_prime,
    ``DkMath.FLT.Kummer.fermatLastTheoremFor_of_regular_prime,
    ``DkMath.FLT.Kummer.fermatLastTheoremFor_eleven,
    ``DkMath.FLT.Kummer.fermatLastTheoremFor_thirteen,
    ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_eleven,
    ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_thirteen]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} new explicit declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.phase_sum_dvd_iff #[] true
  checkRoot ``DkMath.FLT.Kummer.not_int_solution_caseI #[
    ``DkMath.FLT.Kummer.GN_kummer_structure_of_first_case,
    ``DkMath.FLT.Kummer.orient_first_case,
    ``DkMath.FLT.Kummer.CaseIConjugation.packet_of_factor,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_inv_conj_is_root_of_unity,
    ``DkMath.Lib.NumberTheory.four_phase_obstruction,
    ``DkMath.Lib.NumberTheory.dvd_phase_coefficients_of_zero]
  checkRoot ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_eleven #[
    ``DkMath.FLT.Kummer.fermatLastTheoremFor_of_regular_prime,
    ``DkMath.FLT.Kummer.not_int_solution_caseI,
    ``DkMath.FLT.Kummer.positive_state_of_second_case,
    ``DkMath.FLT.Kummer.orient_second_case,
    ``DkMath.FLT.Kummer.RegularDescent.initial_state_of_int_solution,
    ``DkMath.FLT.Kummer.RegularDescent.no_state,
    ``DkMath.FLT.Kummer.RegularDescent.descent_step,
    ``DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.eleven_pid]
  checkRoot ``DkMath.FLT.Kummer.fermatLastTheoremWith_int_thirteen #[
    ``DkMath.FLT.Kummer.fermatLastTheoremFor_of_regular_prime,
    ``DkMath.FLT.Kummer.not_int_solution_caseI,
    ``DkMath.FLT.Kummer.positive_state_of_second_case,
    ``DkMath.FLT.Kummer.orient_second_case,
    ``DkMath.FLT.Kummer.RegularDescent.initial_state_of_int_solution,
    ``DkMath.FLT.Kummer.RegularDescent.no_state,
    ``DkMath.FLT.Kummer.RegularDescent.descent_step,
    ``DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.thirteen_pid]

end PhaseRigidityFLTDependencyAudit
