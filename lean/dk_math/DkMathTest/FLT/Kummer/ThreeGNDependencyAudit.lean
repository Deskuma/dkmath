/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ThreeGNDescent
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.ThreeGNDependencyAudit"

/-!
# 三次 GN 証明の再帰的依存監査

import された定理の名前の列挙ではなく、終点のカーネル型と宣言本体を辿る。
opaque な定理本体と帰納型の構築子も検査する。既存 FLT3 の完成済み終点・
従来の三乗抽出とセクター排除を禁止し、GN のイデアル冪抽出、単元補題、
環同型、新しい厳密降下が実際の依存先であることも要求する。
-/

namespace ThreeGNDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx ||
  s.startsWith "fermatLastTheoremThree" ||
  s.contains "Mathlib.NumberTheory.FLT.Three" ||
  s.startsWith "FermatLastTheoremForThree" ||
  #["DkMath.FLT.FLT3_core",
    "DkMath.FLT.Three.fermatThree_no_positive_solution",
    "DkMath.FLT.Three.FLT_d3_unconditional",
    "DkMath.FLT.Three.primitiveCubicPack_false",
    "DkMath.FLT.Three.exists_smaller_primitiveCubicPack",
    "DkMath.FLT.Three.primitiveCubicStrictDescent",
    "DkMath.FLT.Three.eisensteinDescentFactorSource_of_primitive_solution",
    "DkMath.FLT.Three.exists_unit_mul_cube_of_coprime_mul_eq_cube",
    "DkMath.FLT.Three.beta_eq_cube",
    "DkMath.FLT.Three.sector_eq_one",
    "DkMath.FLT.Three.tau_sector_false",
    "DkMath.FLT.Three.tauSq_sector_false"].contains s

private def checkRoot (root : Name) : CommandElabM Unit := do
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
      ``DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv,
      ``DkMath.Lib.NumberTheory.exists_ideal_pow_of_stripped_phaseFactor,
      ``DkMath.FLT.Kummer.cubic_kummer_unit_power_criterion,
      ``DkMath.FLT.Kummer.exists_GN_cubic_factor_eq_zeta_sub_one_mul_cube,
      ``DkMath.FLT.Kummer.exists_cube_eq_stripped_beta,
      ``DkMath.FLT.Kummer.gnPrimitiveCubicStrictDescent,
      ``DkMath.FLT.Three.nonempty_primitiveCubicStrictDescent_of_factors] do
    unless visited.contains required do throwError "Required provider absent: {required}"
  logInfo m!"ROOT: {root}"
  logInfo m!"reachable constants: {visited.size}; readable bodies: {bodies}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo "PASS: required GN/ideal/unit/equivalence/descent providers present; forbidden, missing, unreadable lists empty."

set_option maxHeartbeats 0 in
-- Recursively inspect the complete proof graph, including opaque bodies and constructors.
run_cmd checkRoot ``DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN

end ThreeGNDependencyAudit
