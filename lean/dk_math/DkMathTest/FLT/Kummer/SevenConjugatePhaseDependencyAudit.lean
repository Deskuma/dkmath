/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenKummerUnit
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.SevenConjugatePhaseDependencyAudit"

/-!
# 共役位相・単元七乗性・GN 因子復元の再帰的依存監査

型・opaque 本体・帰納型の構築子を辿る。一般 FLT、既存 FLT3/5 の完成終点、
三次・五次の単元 criterion に依存しないことと、実三次判定・CM 位相解析を
実際に消費することを同時に確認する。
-/

namespace SevenConjugatePhaseDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "fermatLastTheorem" || s.startsWith "FltRegular." ||
  s.contains "fermatThree_no_positive_solution" || s.contains "fermatFive_no_positive_solution" ||
  s.contains "fermatSeven_no_positive_solution" ||
  #["DkMath.FLT.Kummer.cubic_kummer_unit_power_criterion",
    "DkMath.FLT.Kummer.quintic_kummer_unit_power_criterion"].contains s

private def checkRoot (root : Name) (requireIdeal : Bool) : CommandElabM Unit := do
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
  for required in #[
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.integralConj_eq_CM,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.septic_rootOfUnity_eq_one_of_congruent,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.conjugateRatio_eq_one,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.relativeNorm_primary_unit_seventh,
      ``DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero,
      ``NumberField.IsCMField.unitsMulComplexConjInv,
      ``DkMath.Lib.Algebra.oddPower_root_of_square] do
    unless visited.contains required do throwError "Required provider absent: {required}"
  if requireIdeal then
    for required in #[
        ``DkMath.Lib.NumberTheory.exists_ideal_pow_of_stripped_phaseFactor,
        ``DkMath.FLT.Kummer.SevenPrimaryNorm.septic_kummer_unit_power_criterion] do
      unless visited.contains required do throwError "Required ideal/unit provider absent: {required}"
  logInfo m!"ROOT: {root}; ideal extraction required: {requireIdeal}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required norm/CM/phase providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Three complete proof graphs are traversed, including opaque bodies and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Kummer.SevenPrimaryNorm.septic_kummer_unit_power_criterion false
  checkRoot ``DkMath.FLT.Kummer.SevenPrimaryNorm.GN_primary_unit_seventh false
  checkRoot ``DkMath.FLT.Kummer.SevenPrimaryNorm.exists_GN_septic_factor_eq_zeta_sub_one_mul_seventh true

end SevenConjugatePhaseDependencyAudit
