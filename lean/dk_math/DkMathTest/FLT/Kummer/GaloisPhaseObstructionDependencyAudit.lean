/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.GaloisPhaseObstruction
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.GaloisPhaseObstructionDependencyAudit"

/-!
# IRR-006 実依存監査

型と opaque 証明項も含む推移閉包をたどる。真のガロア供給・イデアル写像・
イデアル冪の単射性を要求し、大域的な正則性供給と未証明の外部橋を禁止する。
-/

namespace GaloisPhaseObstructionDependencyAudit
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
-- Traverse the complete large proof graphs, including opaque bodies and field equivalences.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.mapNonzeroIdeal,
    ``DkMath.Lib.NumberTheory.classGroup_map_mk0,
    ``DkMath.Lib.NumberTheory.classGroup_map_refl,
    ``DkMath.Lib.NumberTheory.classGroup_map_trans,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.transport,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.obstruction_transport,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.root_transport_of_unit,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.obstruction_transport_of_unit,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.transport,
    ``DkMath.Lib.NumberTheory.PhaseClassPacket.obstruction_transport,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phaseMul,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phaseMul_cast,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phaseMul_one,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phaseMul_mul,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phasePerm,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phaseMul_zero,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.zeta_phaseMul,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.quotient_galois,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phase_root_galois,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phase_obstruction_galois,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma_mul,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma_int,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma_zeta,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.exists_ramifier_unit,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.obstruction_int,
    ``DkMath.FLT.Kummer.IrregularDescent.ObstructedState.galois_transport,
    ``DkMath.FLT.Kummer.IrregularPrime37.sigma37,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_galois]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public IRR-006 declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phase_obstruction_galois #[
    ``DkMath.Lib.NumberTheory.classGroup_map_mk0,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.root_transport_of_unit,
    ``Ideal.map, ``pow_left_injective] true true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.obstruction_int #[
    ``NumberField.RingOfIntegers.mapRingEquiv,
    ``IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.exists_ramifier_unit,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.quotient_galois] true true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_galois #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observe,
    ``DkMath.FLT.Kummer.RegularDescent.State.quotient_ideal_power,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phase_root_galois,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma_zeta] false true

end GaloisPhaseObstructionDependencyAudit
