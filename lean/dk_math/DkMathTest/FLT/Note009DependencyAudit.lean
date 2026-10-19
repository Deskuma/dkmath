/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Note009Transport
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note009DependencyAudit"

/-!
# NOTE-009: 実際の指標輸送・Bernoulli証明書・反例の構成的正規化を監査する

共通因子の抽出と符号付き置換を辿り、FLT終点からの空虚なSource構成を禁止する。
指標5の同定には有限Bernoulli計算を許し、非零成分の算術的存在を外部供給しない。
-/
namespace Note009DependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
    s.toLower.contains "herbrand" || s.toLower.contains "ribet" ||
    s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
    s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution"

private def globalProvider (n : Name) : Bool :=
  (#[`DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt,
    `DkMath.Lib.NumberTheory.KummerUnitPowerCriterion,
    `DkMath.FLT.Kummer.RegularDescent.Conditions,
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
-- Traverse actual types and opaque bodies across the class-group and local-reduction proof graphs.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character_ext,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character_generator_pow,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.action_apply_component,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_action_commute,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_action,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_action_eq_zero_iff,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.characterSupport,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.mem_characterSupport,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.characterSupport_action,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32Label,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_character,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_character_ne_one,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32Label_ne_one,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_residual_exponent,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_target_certificate,
    ``DkMath.FLT.Kummer.IrregularPrime37.observeVector_galois,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_projector_galois,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_characterSupport_galois,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_nonzero_characterSupport_eq,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_nonzero_projector_iff,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_projector,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_bernoulli32_projector_galois,
    ``DkMath.FLT.Frey.coprime_of_primitive_equation,
    ``DkMath.FLT.Frey.PrimitiveReduction,
    ``DkMath.FLT.Frey.exists_primitiveReduction,
    ``DkMath.FLT.Frey.coprime_right_of_equation,
    ``DkMath.FLT.Frey.ParityTrace,
    ``DkMath.FLT.Frey.orient_parity,
    ``DkMath.FLT.Frey.OrientationTrace,
    ``DkMath.FLT.Frey.odd_mod_four_orientation,
    ``DkMath.FLT.Frey.exists_source_of_coprime,
    ``DkMath.FLT.Frey.exists_source_of_counterexample,
    ``DkMath.FLT.Frey.Source.ofCounterexample,
    ``DkMath.FLT.Frey.Source.ofCounterexample_spec,
    ``DkMath.FLT.Frey.Source.ofCounterexample_local_profile,
    ``DkMath.FLT.Frey.PrimitiveReduction.mk,
    ``DkMath.FLT.Frey.PrimitiveReduction.scale,
    ``DkMath.FLT.Frey.PrimitiveReduction.scale_ne,
    ``DkMath.FLT.Frey.PrimitiveReduction.A,
    ``DkMath.FLT.Frey.PrimitiveReduction.B,
    ``DkMath.FLT.Frey.PrimitiveReduction.C,
    ``DkMath.FLT.Frey.PrimitiveReduction.a_eq,
    ``DkMath.FLT.Frey.PrimitiveReduction.b_eq,
    ``DkMath.FLT.Frey.PrimitiveReduction.c_eq,
    ``DkMath.FLT.Frey.PrimitiveReduction.A_ne,
    ``DkMath.FLT.Frey.PrimitiveReduction.B_ne,
    ``DkMath.FLT.Frey.PrimitiveReduction.C_ne,
    ``DkMath.FLT.Frey.PrimitiveReduction.coprime,
    ``DkMath.FLT.Frey.PrimitiveReduction.equation]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public NOTE-009 declarations, including reduction constructor and fields; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_action #[
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.mem_component_iff,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_action,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_action_commute] true true
  checkRoot ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.characterSupport_action #[
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_action_eq_zero_iff,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.characterSupport] true true
  checkRoot ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_target_certificate #[
    ``DkMath.Lib.NumberTheory.BernoulliPrime37.irregular_pair_thirtySeven_iff,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character_generator_pow] true true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_nonzero_characterSupport_eq #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_galois,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.exists_phaseMul_one,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.characterSupport_action] false true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_bernoulli32_projector_galois #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observeVector_galois,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_character] false true
  checkRoot ``DkMath.FLT.Frey.exists_primitiveReduction #[
    ``Finset.extract_gcd,
    ``DkMath.FLT.Frey.coprime_of_primitive_equation,
    ``DkMath.FLT.Frey.PrimitiveReduction.mk] false true
  checkRoot ``DkMath.FLT.Frey.exists_source_of_coprime #[
    ``DkMath.FLT.Frey.orient_parity,
    ``DkMath.FLT.Frey.odd_mod_four_orientation,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.normalization_of_oriented] false true
  checkRoot ``DkMath.FLT.Frey.Source.ofCounterexample #[
    ``DkMath.FLT.Frey.exists_primitiveReduction,
    ``DkMath.FLT.Frey.exists_source_of_coprime] false true
  checkRoot ``DkMath.FLT.Frey.Source.ofCounterexample_spec #[
    ``DkMath.FLT.Frey.PrimitiveReduction,
    ``DkMath.FLT.Frey.OrientationTrace,
    ``DkMath.FLT.Frey.exists_source_of_counterexample] false true
  checkRoot ``DkMath.FLT.Frey.Source.ofCounterexample_local_profile #[
    ``DkMath.FLT.Frey.Source.ofCounterexample,
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.FLT.Frey.Source.isMinimal_every_prime,
    ``DkMath.FLT.Frey.Source.good_or_multiplicative_every_prime,
    ``DkMath.FLT.Frey.Source.exponent_dvd_valuation_iff_ne_two] false true

#print axioms DkMath.FLT.Frey.Source.ofCounterexample
#print axioms DkMath.FLT.Frey.Source.ofCounterexample_local_profile
#print axioms DkMath.FLT.Kummer.IrregularPrime37.observe_nonzero_characterSupport_eq
#print axioms DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.bernoulli32_target_certificate

end Note009DependencyAudit
