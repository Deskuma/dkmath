/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace

#print "file: DkMathTest.FLT.Note032NumberFieldUnitTraceDependencyAudit"

namespace Note032NumberFieldUnitTraceDependencyAudit

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
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.unitsMap_torsion_le #[``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.unitsMap]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.quotMap_mk #[``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.unitsMap_torsion_le]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.freeUnitAction #[``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.unitsMap_mul, ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.quotMapLin]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.trace_vMap #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.exists_unitClass_basis, ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.quotMapLin]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logFull_eq_zero_iff #[``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logFull]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logQuot_quotMap #[``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logFull_unitsMap, ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.unitsMap]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_funLeft #[``LinearMap.trace_eq_matrix_trace]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_quotMap_eq #[``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_funLeft, ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logQuot_quotMap, ``NumberField.Units.basisModTorsion]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_vMap_eq_exponent_add_fixedPlaces #[``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_quotMap_eq, ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.trace_vMap]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.integerAut_on_pth_roots #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.characterEquiv_symm_root]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_unitAction_eq_character_add_fixedPlaces #[``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_vMap_eq_exponent_add_fixedPlaces, ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.integerAut_on_pth_roots, ``NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.freeUnitAction #[`F] #[`hdiv, `n, `hσ, `htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace.trace_vMap #[`p, `F, `hdiv, `σ, `n, `hσ] #[`htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logFull_eq_zero_iff #[`F] #[`hdiv, `hσ, `htrace, `hrank]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.logQuot_quotMap #[`F, `σ, `x] #[`htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_quotMap_eq #[`F, `σ] #[`p, `hdiv, `n, `hσ, `htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_vMap_eq_exponent_add_fixedPlaces #[`F, `p, `hdiv, `σ, `n, `hσ] #[`htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.integerAut_on_pth_roots #[`hζ, `d, `x, `hx] #[`hσ, `n, `htrace, `hrank]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_unitAction_eq_character_add_fixedPlaces #[`hζ, `d] #[`hp5, `hdiv, `n, `hσ, `htrace, `hrank, `hunit, `hfixed]

end Note032NumberFieldUnitTraceDependencyAudit
