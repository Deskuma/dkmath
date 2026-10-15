/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveGNDescent
import Lean.Util.FoldConsts

/-!
# 五次 GN 証明の二つの境界での再帰的依存監査

同じ β の根の復元では、従来の黄金比環の五乗抽出も禁止する。
終点では降下内部の lift の再抽出を明示的に許可し、その存在を確認する。
両方とも既存 FLT5 の完成済み終点と既存パケットの初期セクター排除は禁止する。
型・opaque 本体・帰納型の構築子まで辿り、単なる import 監査とは区別する。
-/

open Lean Elab Command

namespace FiveGNDependencyAudit

private def forbidden (n : Name) (allowReentry : Bool) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheoremFive" ||
  s.contains "Mathlib.NumberTheory.FLT.Five" ||
  #["DkMath.FLT.Five.flt5Target", "DkMath.FLT.Five.fermatFive_no_positive_solution",
    "DkMath.FLT.Five.goldenZeroSectorDescentPacket_false",
    "DkMath.FLT.Five.goldenZeroSectorCandidate_false",
    "DkMath.FLT.Five.goldenZeroSectorArithmeticExclusion",
    "DkMath.FLT.Five.goldenZeroSectorFactorExclusion",
    "DkMath.FLT.Five.signedGoldenFifthPowerUpToUnitCore",
    "DkMath.FLT.Five.signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor",
    "DkMath.FLT.Five.signedGoldenFiniteUnitSectorCore_of_unitClasses",
    "DkMath.FLT.Five.signedGolden_nonzero_unitSector_false"].contains s ||
  (!allowReentry && s == "DkMath.FLT.Five.goldenCoprimeFactorOfFifthPower")

private def checkRoot (root : Name) (allowReentry : Bool) : CommandElabM Unit := do
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
    if forbidden n allowReentry then throwError "Forbidden dependency: {n}"
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
  for required in #[
      ``DkMath.Lib.NumberTheory.quinticGoldenEquiv,
      ``DkMath.Lib.NumberTheory.exists_ideal_pow_of_stripped_phaseFactor,
      ``DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion,
      ``NumberField.IsCMField.unitsMulComplexConjInv,
      ``DkMath.FLT.Five.goldenUnitClassesModFifth,
      ``DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_via_GN] do
    unless visited.contains required do throwError "Required provider absent: {required}"
  if allowReentry then
    for required in #[
        ``DkMath.FLT.Five.GoldenZeroSectorDescentPacket.strictDescent,
        ``DkMath.FLT.Five.GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower] do
      unless visited.contains required do throwError "Required descent re-entry absent: {required}"
  logInfo m!"ROOT: {root}; legacy lift re-entry allowed: {allowReentry}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required GN/ideal/unit/relative-norm providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Two complete proof graphs are traversed, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.exists_fifth_eq_stripped_beta_via_GN false
  checkRoot ``DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN true

end FiveGNDependencyAudit
