/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateVector

#print "file: DkMathTest.FLT.Note032FreyCyclicTateVectorDependencyAudit"

namespace Note032FreyCyclicTateVectorDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "P2M." || s.startsWith "P2MW." ||
    s.startsWith "FltRegular." || s.startsWith "FreyPackage." ||
    s.startsWith "DkMath.FLT.Kummer." || s.contains "fermatLastTheorem" ||
    s.contains "fermat_last_theorem" || s.contains "fermatFive_no_positive_solution"

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
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  for n in required do
    unless visited.contains n do throwError "Required theorem absent: {n}"
  logInfo m!"PASS: {root}; {visited.size} reachable constants; required actual theorems present."

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | .letE n _ _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input absent in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; remaining arithmetic inputs explicit."

set_option maxHeartbeats 0 in
-- Twelve finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.map_injective #[``DkMath.Lib.Algebra.PrimePowerTateSequence.map]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.action #[``DkMath.Lib.Algebra.PrimePowerTateSequence.map]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateGenerators #[``DkMath.FLT.Frey.Source.residualCyclicTower_lift, ``DkMath.FLT.Frey.Source.residualTateSeed]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateGenerators_order #[``addOrderOf_eq_prime_pow, ``DkMath.FLT.Frey.Source.residualTateGenerators_to_seed]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateGenerators_generate #[``Nat.card_zmultiples, ``DkMath.FLT.Frey.Source.residualTateGenerators_order]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTate_inclusion_injective #[``DkMath.FLT.Frey.Source.residualCyclicTate]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateAction #[``DkMath.FLT.Frey.Source.residualCyclicTate_stable, ``DkMath.Lib.Algebra.PrimePowerTateSequence.action]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTate_inclusion_equivariant #[``DkMath.FLT.Frey.Source.residualCyclicTateAction]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateVector #[``DkMath.FLT.Frey.Source.residualTateGenerators_step, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateVector_ne_zero #[``DkMath.FLT.Frey.Source.residualTateSeed_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateVector_fixed_iff #[``DkMath.FLT.Frey.Source.residualTateGenerators_generate, ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_eq_one_iff, ``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateVector_frobenius_moved #[``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_frobenius_ne_one, ``DkMath.FLT.Frey.Source.residualCyclicTateVector_fixed_iff]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.sequences #[`p, `G] #[`hprime, `hfinite, `hnext]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.map_injective #[`f, `hf] #[`hmap]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.action #[`ρ] #[`hact]
  checkInputs ``DkMath.FLT.Frey.Source.residualPointActionHom #[`S] #[`hclass, `hbad, `hact]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateGenerators #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hgen, `hnext, `hvector]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateGenerators_order #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n] #[`horder, `hgen]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateAction #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hact, `hstable]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateVector_ne_zero #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hnonzero, `hvector]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateVector_fixed_iff #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hfixed, `hscalar, `hchar]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateVector_frobenius_moved #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hell, `hellp, `hgood, `A, `hA, `σ, `hσ] #[`hmoved, `hchar, `hfixed]

end Note032FreyCyclicTateVectorDependencyAudit
