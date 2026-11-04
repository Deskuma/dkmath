/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank

#print "file: DkMathTest.FLT.Note032CyclotomicOmegaSquareUnitRankDependencyAudit"

namespace Note032CyclotomicOmegaSquareUnitRankDependencyAudit

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
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitClassFinite #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitProjection_surjective]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.exists_unitClass_basis #[``NumberField.Units.exist_unique_eq_mul_prod, ``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitProjection_eq_zero_iff]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.finrank_unitClass #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.exists_unitClass_basis]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.finrank_unitClass_cyclotomic #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.finrank_unitClass, ``NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.unitClass_finite #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitClassFinite]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finite #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitClassFinite]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.root_unitClass_finrank #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.finrank_unitClass_cyclotomic, ``DkMath.Lib.NumberTheory.CyclotomicKernelField.rootField_isCyclotomic]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_pos #[``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitClassFinite, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.projectedCyclotomicUnit_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_lt_prime #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.root_unitClass_finrank]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.trace_omegaSquareProjector_eq_finrank #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_idempotent, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_range]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_eq_one_of_trace #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.trace_omegaSquareProjector_eq_finrank, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_lt_prime]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.trace_eq_one_iff_finrank_eq_one #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_eq_one_of_trace]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.primaryWeightSquareSpace_eq_bot_of_trace #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_eq_one_of_trace, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryWeightSquareSpace_eq_bot_of_rank_one]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.unitClassFinite #[`p] #[`hdiv, `hrank, `htrace, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension.finrank_unitClass #[`hdiv] #[`hrank, `htrace, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.finrank_unitClass_cyclotomic #[`hζ, `hp5] #[`hdiv, `hrank, `htrace, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.root_unitClass_finrank #[`hζ, `hp5] #[`hdiv, `hrank, `htrace, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_pos #[`hζ, `hp5] #[`hrank, `htrace, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.trace_omegaSquareProjector_eq_finrank #[`hζ] #[`hrank, `htrace, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_eq_one_of_trace #[`hζ, `hp5, `htrace] #[`hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.primaryWeightSquareSpace_eq_bot_of_trace #[`hζ, `hp5, `htrace] #[`hrank, `g, `hdetect, `hunit]

end Note032CyclotomicOmegaSquareUnitRankDependencyAudit
