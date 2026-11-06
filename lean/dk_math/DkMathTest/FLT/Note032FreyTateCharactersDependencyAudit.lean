/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCharactersModP

#print "file: DkMathTest.FLT.Note032FreyTateCharactersDependencyAudit"

namespace Note032FreyTateCharactersDependencyAudit

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
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.second #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.secondHom]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.offDiagonal_mul #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.first, ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.second]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.determinant #[``Matrix.det_fin_two]
  checkRoot ``DkMath.Lib.Algebra.PadicCharacterLimit.continuous_of_reduction_kernels #[``DkMath.Lib.Algebra.PadicCharacterLimit.character_unique, ``DkMath.Lib.Algebra.PadicCharacterLimit.character_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateMatrixRepresentation #[``DkMath.Lib.Algebra.PrimePowerTateSequence.actionLinear, ``DkMath.FLT.Frey.Source.residualTateBasis]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateMatrix_first_character #[``DkMath.FLT.Frey.Source.residualTateActionMatrix_first_column]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.second, ``DkMath.FLT.Frey.Source.residualTateMatrixRepresentation_lower_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecond_coordinate #[``DkMath.FLT.Frey.Source.residualTateEquiv_second]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_level, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairLevelEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel_isOpen #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen_of_ne_zero, ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_continuous #[``DkMath.Lib.Algebra.PadicCharacterLimit.continuous_of_reduction_kernels, ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel_isOpen]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_offDiagonal_mul #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.offDiagonal_mul, ``DkMath.FLT.Frey.Source.residualTateMatrix_first_character]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_determinant #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.determinant, ``DkMath.FLT.Frey.Source.residualTateMatrix_first_character]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_mod_prime #[``DkMath.FLT.Frey.Source.residualTateLineReduction_surjective, ``DkMath.FLT.Frey.Source.residualTateEquiv_mem_line_iff, ``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_shiftOfZero, ``DkMath.FLT.Frey.Source.residualTateSecond_coordinate]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_determinant_mod_prime #[``DkMath.FLT.Frey.Source.residualTateSecondCharacter_mod_prime, ``DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod_prime, ``DkMath.FLT.Frey.Source.residualTate_determinant]
  checkInputs ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.second #[`ρ, `ht] #[`hunit, `hchar]
  checkInputs ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.offDiagonal_mul #[`ρ, `ht, `g, `h] #[`hcocycle, `hsplit]
  checkInputs ``DkMath.Lib.Algebra.PadicCharacterLimit.continuous_of_reduction_kernels #[`d, `hopen] #[`hcont]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hunit, `hsecond]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecond_coordinate #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hcoord]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n] #[`hker]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel_isOpen #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n] #[`hopen]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_continuous #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hcont, `hopen]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_offDiagonal_mul #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ, `τ] #[`hcocycle, `hsplit]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_determinant #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hdet]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_mod_prime #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`htrivial, `hmodp, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_determinant_mod_prime #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ] #[`hweil, `hdet]

end Note032FreyTateCharactersDependencyAudit
