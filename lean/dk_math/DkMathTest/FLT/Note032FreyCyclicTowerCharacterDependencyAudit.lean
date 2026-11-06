/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTowerCharacter

#print "file: DkMathTest.FLT.Note032FreyCyclicTowerCharacterDependencyAudit"

namespace Note032FreyCyclicTowerCharacterDependencyAudit

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
-- Eleven finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.CyclicActionCharacter.character #[``DkMath.Lib.Algebra.CyclicActionCharacter.coordinate_action]
  checkRoot ``DkMath.Lib.Algebra.CyclicActionCharacter.action_eq_nsmul #[``DkMath.Lib.Algebra.CyclicActionCharacter.coordinate_action]
  checkRoot ``DkMath.Lib.Algebra.CyclicActionCharacter.character_eq_one_iff #[``DkMath.Lib.Algebra.CyclicActionCharacter.coordinate_action]
  checkRoot ``DkMath.Lib.Algebra.CyclicActionCharacter.character_independent #[``DkMath.Lib.Algebra.CyclicActionCharacter.character_eq_natCast_of_action, ``DkMath.Lib.Algebra.CyclicActionCharacter.action_eq_nsmul]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_spec #[``DkMath.Lib.Algebra.CyclicActionCharacter.action_eq_nsmul, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.action]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_eq_one_iff #[``DkMath.Lib.Algebra.CyclicActionCharacter.character_eq_one_iff]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_kernel_isOpen #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen_of_ne_zero, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_eq_one_iff, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_compatible #[``DkMath.Lib.Algebra.CyclicActionCharacter.character_eq_natCast_of_action, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_spec]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_mod_prime #[``DkMath.FLT.Frey.Source.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_spec, ``DkMath.Lib.Algebra.CyclicActionCharacter.character_eq_natCast_of_action]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.card_le_good_points_of_character_one #[``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.card_fixed_torsion_le_finite_points, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_eq_one_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerCharacter_compatible #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_compatible, ``DkMath.FLT.Frey.Source.residualCyclicTower_step]
  checkInputs ``DkMath.Lib.Algebra.CyclicActionCharacter.character #[`e, `ρ] #[`hfixed, `hchar, `hcompat]
  checkInputs ``DkMath.Lib.Algebra.CyclicActionCharacter.character_independent #[`e, `ρ, `e'] #[`hindependent]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character #[`T] #[`hclass, `hbad, `hchar, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_spec #[`T, `σ, `x, `hx] #[`hclass, `hbad, `hchar]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_eq_one_iff #[`T, `σ] #[`hclass, `hbad, `hchar, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_kernel_isOpen #[`T] #[`hclass, `hbad, `hopen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_compatible #[`T, `U, `hnm, `hTU, `σ] #[`hclass, `hbad, `hcompat]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_mod_prime #[`T, `hline, `hcofixed, `σ] #[`hclass, `hbad, `hmodp]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.card_le_good_points_of_character_one #[`T, `hell, `hellp, `hgood, `A, `hA, `σ, `hσ, `hchar] #[`hclass, `hbad, `hfixed, `habsorb]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTowerCharacter_compatible #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `σ] #[`hcompat, `hchar, `hfixed]

end Note032FreyCyclicTowerCharacterDependencyAudit
