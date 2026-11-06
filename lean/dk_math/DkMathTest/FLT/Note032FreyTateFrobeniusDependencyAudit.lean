/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateFrobenius

#print "file: DkMathTest.FLT.Note032FreyTateFrobeniusDependencyAudit"

namespace Note032FreyTateFrobeniusDependencyAudit

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
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.torsionCyclotomicCharacter_eq_natCast #[``DkMath.Lib.NumberTheory.CyclotomicFrobenius.apply_root_eq_pow]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.prime_power_valuation_eq_one #[]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.padicCyclotomicCharacter_eq_natCast #[``DkMath.Lib.NumberTheory.CyclotomicFrobenius.torsionCyclotomicCharacter_eq_natCast, ``cyclotomicCharacter.toZModPow, ``DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.trace #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.charpoly_factor #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.determinant]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.quadratic #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.matrix_quadratic #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.linear_quadratic #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.matrix_quadratic]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_trace_reduction #[``DkMath.FLT.Frey.Source.residualTate_matrix_reduction]
  checkRoot ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_frobenius #[``DkMath.Lib.NumberTheory.CyclotomicFrobenius.padicCyclotomicCharacter_eq_natCast]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_frobenius_det #[``DkMath.FLT.Frey.Source.residualTate_determinant_cyclotomic, ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_frobenius]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_frobenius_trace #[``DkMath.FLT.Frey.Source.residualTateSecondCharacter_eq_cyclotomic, ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_frobenius]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_frobenius_charpoly #[``DkMath.FLT.Frey.Source.residualTate_frobenius_trace, ``DkMath.FLT.Frey.Source.residualTate_frobenius_det]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_frobenius_relation #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.linear_quadratic, ``DkMath.FLT.Frey.Source.residualTate_frobenius_det]
  checkRoot ``DkMath.FLT.Frey.Source.residualTate_finite_frobenius_relation #[``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.linear_quadratic, ``DkMath.FLT.Frey.Source.residualTate_trace_reduction, ``DkMath.FLT.Frey.Source.residualTate_determinant_finite, ``DkMath.FLT.Frey.Source.residualTate_frobenius_det]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.torsionCyclotomicCharacter_eq_natCast #[`n, `hn, `A, `hunit, `hσ] #[`hvalue]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.prime_power_valuation_eq_one #[`hq, `hqp, `A, `hA, `n] #[`hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.padicCyclotomicCharacter_eq_natCast #[`hq, `hqp, `A, `hA, `hσ] #[`hvalue]
  checkInputs ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.charpoly_factor #[`ρ, `ht, `g] #[`hpoly, `hsplit]
  checkInputs ``DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.linear_quadratic #[`b, `f, `a, `c, `htrace, `hdet, `x] #[`hCH]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_trace_reduction #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `σ] #[`htrace]
  checkInputs ``DkMath.FLT.Frey.Source.tateCyclotomicCharacter_frobenius #[`hq, `hqp, `A, `hA, `hσ] #[`S, `hvalue]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_frobenius_det #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `A, `hA, `hσ] #[`htrace, `hdet, `hCH, `hpointcount, `hpoly]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_frobenius_trace #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `A, `hA, `hσ] #[`htrace, `hdet, `hCH, `hpointcount, `hpoly]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_frobenius_charpoly #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `A, `hA, `hσ] #[`htrace, `hdet, `hCH, `hpointcount, `hpoly]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_frobenius_relation #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `A, `hA, `hσ] #[`htrace, `hdet, `hCH, `hpointcount, `hpoly]
  checkInputs ``DkMath.FLT.Frey.Source.residualTate_finite_frobenius_relation #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `A, `hA, `hσ] #[`htrace, `hdet, `hCH, `hpointcount, `hpoly]

end Note032FreyTateFrobeniusDependencyAudit
