/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateBasis

#print "file: DkMathTest.FLT.Note032FreyTateBasisDependencyAudit"

namespace Note032FreyTateBasisDependencyAudit

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
  checkRoot ``DkMath.Lib.Algebra.PrimePowerTateSequence.pair_span #[``DkMath.Lib.Algebra.PrimePowerTateSequence.evaluation_to_zero]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairLevelEquiv #[``DkMath.Lib.Algebra.PrimePowerTateSequence.pair_span, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairCoefficients_compatible #[``DkMath.Lib.Algebra.PrimePowerTateSequence.compatible, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairLevelEquiv]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_injective #[``DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_surjective #[``DkMath.Lib.Algebra.PrimePowerTateSequence.liftResidues_mod, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairCoefficients_compatible]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairEquiv #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_injective, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateFirstReduction_ne_zero #[``DkMath.FLT.Frey.Source.residualTateSeed_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondResidual_exists #[``DkMath.FLT.Frey.Source.residual_finrank_eq_two, ``DkMath.FLT.Frey.Source.residualTateFirstReduction_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecond #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateReduction_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateResidualBasis #[``DkMath.FLT.Frey.Source.residualTateResidualPair_independent]
  checkRoot ``DkMath.FLT.Frey.Source.residualTatePair_base_span #[``DkMath.FLT.Frey.Source.residualTateResidualBasis, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_smul_val]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateEquiv #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairEquiv, ``DkMath.FLT.Frey.Source.residualTatePair_base_span]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateBasis #[``DkMath.FLT.Frey.Source.residualTateEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateEquiv_mem_line_iff #[``DkMath.FLT.Frey.Source.residualCyclicTateParametrization_surjective, ``DkMath.FLT.Frey.Source.residualTateEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateActionMatrix_first_column #[``DkMath.FLT.Frey.Source.residualCyclicTateLine_action_scalar, ``DkMath.FLT.Frey.Source.residualTateBasis_first, ``DkMath.FLT.Frey.Source.residualTateActionMatrix]
  checkInputs ``DkMath.Lib.Algebra.PrimePowerTateSequence.pair_span #[`v, `w, `hbase, `n, `x, `hx] #[`hfree, `hfinite, `hrank]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairLevelEquiv #[`E, `v, `w, `hbase, `n] #[`hbij, `hcard]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairCoefficients_compatible #[`E, `v, `w, `hbase, `x, `n] #[`hcompat]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairEquiv #[`E, `v, `w, `hbase] #[`hrank, `hfree, `hsurj, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondResidual_exists #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hbasis, `hrank]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecond #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hlift]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateResidualBasis #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hbasis]
  checkInputs ``DkMath.FLT.Frey.Source.residualTatePair_base_span #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `x, `hx] #[`hbase]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateEquiv #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hbase, `hrank, `hfree, `hbij]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateBasis #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hbasis, `hfree]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateEquiv_mem_line_iff #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `a, `b] #[`heq]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateActionMatrix_first_column #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`htriangle, `hscalar, `hdet]

end Note032FreyTateBasisDependencyAudit
