/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateLine

#print "file: DkMathTest.FLT.Note032FreyCyclicTateLineDependencyAudit"

namespace Note032FreyCyclicTateLineDependencyAudit

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
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.padicModule #[``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_eq_of_residue, ``DkMath.Lib.Algebra.PrimePowerTateSequence.padicSMul]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.mapLinear #[``DkMath.Lib.Algebra.PrimePowerTateSequence.padicModule]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.actionLinear #[``DkMath.Lib.Algebra.PrimePowerTateSequence.mapLinear]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.liftResidues_mod #[``PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, ``DkMath.Lib.Algebra.PrimePowerTateSequence.residueRepresentatives_dvd]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateLine #[``DkMath.Lib.Algebra.PrimePowerTateSequence.evaluation_smul]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateGeneratorCoordinates #[``DkMath.FLT.Frey.Source.residualTateGenerators_order]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateCoefficient_compatible #[``DkMath.FLT.Frey.Source.residualTateGenerators_step, ``DkMath.FLT.Frey.Source.residualTateCoefficient_spec]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_injective #[``DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive, ``DkMath.FLT.Frey.Source.residualTateGeneratorCoordinates_nat]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_surjective #[``DkMath.Lib.Algebra.PrimePowerTateSequence.liftResidues_mod, ``DkMath.FLT.Frey.Source.residualTateCoefficient_compatible]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateLineEquiv #[``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_injective, ``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateLine_inclusion_injective #[``DkMath.FLT.Frey.Source.residualCyclicTateLine_inclusion]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateLine_action_scalar #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.character_spec, ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod, ``DkMath.Lib.Algebra.PrimePowerTateSequence.evaluation_smul]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateLine_inclusion_scalar #[``DkMath.Lib.Algebra.PrimePowerTateSequence.actionLinear, ``DkMath.FLT.Frey.Source.residualCyclicTateLine_action_scalar]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.padicModule #[`G, `p] #[`hmodule, `hrank, `hfree]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.mapLinear #[`f] #[`hlinear]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.liftResidues #[`c, `hc] #[`hlimit, `hunit]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateLine #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hmodule, `hrank]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateCoefficient_compatible #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `x, `n] #[`hcompat, `hcoeff]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_injective #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hinj, `hfree]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_surjective #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hsurj, `hlimit, `hcoeff]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateLineEquiv #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hequiv, `hrank, `hfree]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateLine_action_scalar #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ, `x] #[`hscalar, `hchar, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateLine_inclusion_scalar #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ, `x] #[`hequivariance, `hscalar]

end Note032FreyCyclicTateLineDependencyAudit
