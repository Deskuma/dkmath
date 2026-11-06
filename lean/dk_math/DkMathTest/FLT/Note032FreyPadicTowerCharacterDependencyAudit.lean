/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPadicTowerCharacter

#print "file: DkMathTest.FLT.Note032FreyPadicTowerCharacterDependencyAudit"

namespace Note032FreyPadicTowerCharacterDependencyAudit

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
-- Thirteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.PadicCharacterLimit.value_mod #[``PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, ``DkMath.Lib.Algebra.PadicCharacterLimit.representatives_dvd]
  checkRoot ``DkMath.Lib.Algebra.PadicCharacterLimit.character #[``DkMath.Lib.Algebra.PadicCharacterLimit.value_mod, ``MonoidHom.toHomUnits]
  checkRoot ``DkMath.Lib.Algebra.PadicCharacterLimit.character_unique #[``DkMath.Lib.Algebra.PadicCharacterLimit.value_mod, ``DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive]
  checkRoot ``DkMath.Lib.Algebra.PadicCharacterLimit.character_eq_one_iff #[``DkMath.Lib.Algebra.PadicCharacterLimit.value_mod]
  checkRoot ``DkMath.Lib.Algebra.PadicCharacterLimit.character_continuous #[``DkMath.Lib.Algebra.PadicCharacterLimit.value_mod, ``PadicInt.norm_le_pow_iff_mem_span_pow]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_bound #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.card_le_good_points_of_character_one]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_count #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_bound]
  checkRoot ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter #[``DkMath.Lib.Algebra.PadicCharacterLimit.character, ``DkMath.FLT.Frey.Source.residualCyclicTowerCharacter_compatible]
  checkRoot ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod #[``DkMath.Lib.Algebra.PadicCharacterLimit.character_mod]
  checkRoot ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_continuous #[``DkMath.Lib.Algebra.PadicCharacterLimit.character_continuous, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_kernel_isOpen]
  checkRoot ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod_prime #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_mod_prime, ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod]
  checkRoot ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_eq_one_iff #[``DkMath.Lib.Algebra.PadicCharacterLimit.character_eq_one_iff, ``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_eq_one_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_frobenius_ne_one #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_count, ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod]
  checkInputs ``DkMath.Lib.Algebra.PadicCharacterLimit.character #[`c, `hc] #[`hlimit, `hunit, `hchar, `hopen]
  checkInputs ``DkMath.Lib.Algebra.PadicCharacterLimit.character_unique #[`c, `hc, `d, `hd] #[`hunique]
  checkInputs ``DkMath.Lib.Algebra.PadicCharacterLimit.character_continuous #[`c, `hc, `hopen] #[`hcont, `hlimit]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_bound #[`T, `hell, `hellp, `hgood, `A, `hA, `σ, `hσ, `hlarge] #[`hclass, `hbad, `hchar, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_count #[`T, `hn, `hellp, `hgood, `hσ] #[`hclass, `hbad, `hchar]
  checkInputs ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hlimit, `hchar, `hcompat]
  checkInputs ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_continuous #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hcont, `hopen]
  checkInputs ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod_prime #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hcyclo, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_eq_one_iff #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hfixed, `hchar]
  checkInputs ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_frobenius_ne_one #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hell, `hellp, `hgood, `A, `hA, `σ, `hσ] #[`hchar, `hfixed, `habsorb]

end Note032FreyPadicTowerCharacterDependencyAudit
