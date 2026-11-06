/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateReduction

#print "file: DkMathTest.FLT.Note032FreyCyclicTateReductionDependencyAudit"

namespace Note032FreyCyclicTateReductionDependencyAudit

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
-- Fifteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_shiftOfZero #[``DkMath.Lib.Algebra.PrimePowerTateSequence.shiftOfZero, ``DkMath.Lib.Algebra.PrimePowerTateSequence.compatible]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_injective #[``DkMath.Lib.Algebra.PrimePowerTateSequence.compatible]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.range_nsmul_eq_reduction_ker #[``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_shiftOfZero, ``DkMath.Lib.Algebra.PrimePowerTateSequence.killed]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.reduction_surjective #[``DkMath.Lib.Algebra.PrimePowerTateSequence.divisionSequence_step, ``DkMath.Lib.Algebra.PrimePowerTateSequence.divisionSequence_killed]
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.quotientEquiv #[``DkMath.Lib.Algebra.PrimePowerTateSequence.range_nsmul_eq_reduction_ker, ``DkMath.Lib.Algebra.PrimePowerTateSequence.reduction_surjective]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateReduction_surjective #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective, ``DkMath.Lib.Algebra.PrimePowerTateSequence.reduction_surjective]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModPLinearEquiv #[``DkMath.Lib.Algebra.PrimePowerTateSequence.quotientEquiv]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModP_finrank #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModPLinearEquiv, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finrank_torsion_prime]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateModP_finrank #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModP_finrank]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateLine_p_saturated #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_iff_killed_in_later, ``DkMath.Lib.Algebra.PrimePowerTateSequence.compatible]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateLineReduction_surjective #[``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_divisible, ``DkMath.FLT.Frey.Source.residualUnionTateLineEquiv, ``DkMath.Lib.Algebra.PrimePowerTateSequence.reduction_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateLineReduction_ker #[``DkMath.FLT.Frey.Source.residualCyclicTateLine_p_saturated, ``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_shiftOfZero]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateLineModPLinearEquiv #[``DkMath.FLT.Frey.Source.residualTateLineReduction_ker, ``DkMath.FLT.Frey.Source.residualTateLineReduction_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateLineModP_finrank #[``DkMath.FLT.Frey.Source.residualTateLineModPLinearEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateLineReduction_inclusion #[``DkMath.FLT.Frey.Source.residualTateLineReduction, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateReduction]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.range_nsmul_eq_reduction_ker #[`G, `p] #[`hdiv, `hfree, `hker]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.reduction_surjective #[`hdiv] #[`hsurj, `hlift]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateReduction_surjective #[`E, `p] #[`hdiv, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModP_finrank #[`E, `p] #[`hrank, `hfree]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateModP_finrank #[`S] #[`hclass, `hbad, `hrank]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateLine_p_saturated #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `x] #[`hsat, `hfree]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateLineReduction_surjective #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hsurj, `hdiv, `hlift]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateLineReduction_ker #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hker, `hsat]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateLineModPLinearEquiv #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hequiv, `hrank]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateLineModP_finrank #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hrank]
  checkInputs ``DkMath.FLT.Frey.Source.residualTowerUnion_nsmul_surjective #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hdiv, `hsurj]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateLineReduction_inclusion #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `x] #[`hdiagram]

end Note032FreyCyclicTateReductionDependencyAudit
