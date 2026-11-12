/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCyclotomicDeterminant

#print "file: DkMathTest.FLT.Note032FreyTateCyclotomicDeterminantDependencyAudit"

namespace Note032FreyTateCyclotomicDeterminantDependencyAudit

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
-- Inspect checked types, constructors and opaque proof values.
run_cmd do
  checkRoot ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coordinates #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coefficient_injective #[``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coordinates]
  checkRoot ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.map_eq_det_smul #[``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coordinates]
  checkRoot ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.det_eq_of_equivariant #[``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coefficient_injective]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionCyclotomicCharacter_spec #[]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_all #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.geometricWeilPairingData, ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.det_eq_of_equivariant, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionCyclotomicCharacter_spec]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateFiniteBasis #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairLevelEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_coordinate_reduction #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_level]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_basis_reduction #[``DkMath.FLT.Frey.Source.residualTateEquiv_first, ``DkMath.FLT.Frey.Source.residualTateEquiv_second]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_matrix_reduction #[``DkMath.FLT.Frey.Source.residualTate_coordinate_reduction, ``DkMath.FLT.Frey.Source.residualTate_basis_reduction]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_determinant_finite #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_all, ``DkMath.FLT.Frey.Source.residualTate_matrix_reduction]
  checkRoot ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter #[``cyclotomicCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_mod #[``cyclotomicCharacter.toZModPow]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_determinant_cyclotomic #[``DkMath.FLT.Frey.Source.residualTate_determinant_finite, ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_mod, ``DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_eq_cyclotomic #[``DkMath.FLT.Frey.Source.residualTate_determinant, ``DkMath.FLT.Frey.Source.residualTate_determinant_cyclotomic]
  checkInputs ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coefficient_injective #[`e, `halt, `b, `hnd] #[`hfield, `hfaithful]
  checkInputs ``DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.map_eq_det_smul #[`e, `halt, `b, `f] #[`hdet]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_all #[`E, `n, `hn, `b, `σ] #[`hpairing, `hnd, `hprim, `hdet]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionCyclotomicCharacter #[`n, `hn] #[`S]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateFiniteBasis #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_coordinate_reduction #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `x, `n, `i] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_basis_reduction #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `j] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_matrix_reduction #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `σ, `i, `j] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_determinant_finite #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `σ] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_determinant_cyclotomic #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_eq_cyclotomic #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hdet, `hweil, `hprim, `hcyclo, `hratio]
  checkInputs ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_mod #[`n, `σ] #[`S, `hdet]

end Note032FreyTateCyclotomicDeterminantDependencyAudit
