/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.IrregularObstruction
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.IrregularObstructionDependencyAudit"

/-! Actual proof graphs must construct ideal roots and weighted successors without a
regular Conditions provider, old global-root extraction, completed FLT, or new axioms. -/

namespace IrregularObstructionDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
    s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
    s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution"

private def globalProvider (n : Name) : Bool :=
  (#[`DkMath.FLT.Kummer.RegularDescent.Conditions,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_quotient_roots,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_descent_roots,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_weighted_successor,
    `DkMath.FLT.Kummer.RegularDescent.descent_step,
    `DkMath.FLT.Kummer.RegularDescent.no_state,
    `DkMath.FLT.Kummer.RegularDescent.ratio_power,
    `DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    `DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt]).any (fun root => root.isPrefixOf n)

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) (localOnly : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n || (localOnly && globalProvider (privateToUserName n)) ||
        (neutral && (privateToUserName n).toString.startsWith "DkMath.FLT.") then throwError "Forbidden dependency: {n}"
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
-- Audit all public IRR declarations and the large finite transitive proof graphs.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.obstruction,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.torsion,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.trivial_iff_principal,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.trivial_of_torsionFree,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.exists_unit_generator,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.trivial_iff_generator,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.not_principal_of_nontrivial,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.nonzero,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.obstruction_independent,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.trivial_of_unit_power,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.trivial_iff_unit_power,
    ``DkMath.Lib.NumberTheory.HasClassGroupPTorsion,
    ``DkMath.Lib.NumberTheory.hasClassGroupPTorsion_iff_not_torsionFree,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.obstruction,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.torsion,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.trivial_of_torsionFree,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.exists_roots_of_trivial,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.unitScale,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.obstruction_unitScale,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.mul,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.obstruction_mul,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.reindex,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.obstruction_reindex,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.product,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.obstruction_product,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.product_obstruction_eq_one,
    ``DkMath.Lib.NumberTheory.unitPowerObstruction,
    ``DkMath.Lib.NumberTheory.unitPowerObstruction_eq_one_iff,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket.obstruction,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket.exists_power_of_trivial,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket.ratioObstruction,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket.ratio_trivial_iff,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket.obstruction_independent,
    ``DkMath.Lib.NumberTheory.UnitObstructionPacket.trivial_of_power,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.exists_unit_packet,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.bernoulli_thirtyTwo,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.thirtySeven_dvd_numerator,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.thirtySeven_not_dvd_denominator,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.BernoulliIrregularPair,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.irregular_pair_thirtySeven_iff,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.no_irregular_pair_eleven,
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.no_irregular_pair_thirteen,
    ``DkMath.Lib.Cosmic.pow_seven_small,
    ``DkMath.Lib.Cosmic.pow_thirtySeven_small,
    ``DkMath.Lib.Cosmic.thirtySeven_difference_left,
    ``DkMath.Lib.Cosmic.thirtySeven_difference_right,
    ``DkMath.Lib.Cosmic.prime_choose_exact_layer,
    ``DkMath.Lib.Cosmic.prime_interior_content,
    ``DkMath.Lib.Cosmic.thirtySeven_choose_exact_layer,
    ``DkMath.Lib.Cosmic.interior_contents_eleven_thirteen_thirtySeven,
    ``DkMath.Lib.Cosmic.thirtySeven_initial_coefficients,
    ``DkMath.Lib.Cosmic.prime_GN_zmod,
    ``DkMath.Lib.Cosmic.thirtySeven_GN_exact_layer,
    ``DkMath.FLT.Kummer.IrregularDescent.ObstructedState,
    ``DkMath.FLT.Kummer.IrregularDescent.ofState,
    ``DkMath.FLT.Kummer.IrregularDescent.ofState_source,
    ``DkMath.FLT.Kummer.IrregularDescent.ObstructedState.product_obstruction_one,
    ``DkMath.FLT.Kummer.IrregularDescent.ObstructedState.three_term,
    ``DkMath.FLT.Kummer.IrregularDescent.descent_roots_of_phase_roots,
    ``DkMath.FLT.Kummer.IrregularDescent.WeightedObstructedState,
    ``DkMath.FLT.Kummer.IrregularDescent.WeightedObstructedState.unitObstruction,
    ``DkMath.FLT.Kummer.IrregularDescent.WeightedObstructedState.normalize,
    ``DkMath.FLT.Kummer.IrregularDescent.ObstructedState.exists_weighted,
    ``DkMath.FLT.Kummer.IrregularPrime37.Cyclotomic37,
    ``DkMath.FLT.Kummer.IrregularPrime37.phase37,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe,
    ``DkMath.FLT.Kummer.IrregularPrime37.product_obstruction_one,
    ``DkMath.FLT.Kummer.IrregularPrime37.exists_weighted_of_phase_trivial,
    ``DkMath.FLT.Kummer.IrregularPrime37.conditions_incompatible_with_torsion]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public IRR/sample declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.IdealPowerObstruction.trivial_iff_unit_power #[] true true
  checkRoot ``DkMath.FLT.Kummer.IrregularDescent.ofState #[
    ``DkMath.FLT.Kummer.RegularDescent.State.quotient_ideal_power,
    ``DkMath.FLT.Kummer.RegularDescent.State.quotient_product] false true
  checkRoot ``DkMath.FLT.Kummer.IrregularDescent.ObstructedState.exists_weighted #[
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.exists_roots_of_trivial,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.exists_unit_generator,
    ``DkMath.FLT.Kummer.IrregularDescent.descent_roots_of_phase_roots,
    ``DkMath.FLT.Kummer.RegularDescent.quotient_three_term] false true
  checkRoot ``DkMath.FLT.Kummer.IrregularDescent.WeightedObstructedState.normalize #[
    ``DkMath.Lib.NumberTheory.unitPowerObstruction_eq_one_iff,
    ``DkMath.FLT.Kummer.RegularDescent.normalize_weighted] false true
  checkRoot ``DkMath.Lib.NumberTheory.BernoulliPrime37.irregular_pair_thirtySeven_iff #[
    ``bernoulli, ``bernoulli'] true true
  checkRoot ``DkMath.Lib.Cosmic.prime_choose_exact_layer #[] true true

end IrregularObstructionDependencyAudit
