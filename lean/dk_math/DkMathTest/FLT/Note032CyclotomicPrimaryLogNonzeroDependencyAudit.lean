/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicPrimaryLogSplit

#print "file: DkMathTest.FLT.Note032CyclotomicPrimaryLogNonzeroDependencyAudit"

namespace Note032CyclotomicPrimaryLogNonzeroDependencyAudit

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
-- Fourteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_mem #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.unitAction]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_eq_self #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card_isUnit]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_idempotent #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_mem, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_eq_self]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_range #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_mem, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_eq_self]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.characterEquiv #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.characterEquiv_symm_root #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.characterEquiv]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.unitLog_conjugate #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.tlog_conj_eval, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.cyclotomicUnit_val]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.e2_sum #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.sum_units_inv, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.scalarMap_apply]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.e2_sum, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.unitLog_conjugate, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_apply_units, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.integerAut_root]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit_ne_zero #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.parameter_sq_ne_zero, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.two_mul_half]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.projectedCyclotomicUnit_ne_zero #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.weightSquareSpace_ne_bot #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.projectedCyclotomicUnit_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryWeightSquareSpace_eq_bot_of_rank_one #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_unit_rank_one #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryWeightSquareSpace_eq_bot_of_rank_one]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_mem #[`hζ, `x] #[`hcard, `hrank, `hdetect, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_eq_self #[`hζ, `x, `hx] #[`hcard, `hrank, `hdetect, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit #[`hζ, `hp5] #[`hσ, `hrank, `g, `hdetect, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit_ne_zero #[`hζ, `hp5] #[`hrank, `g, `hdetect, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryWeightSquareSpace_eq_bot_of_rank_one #[`hζ, `hp5, `hrank] #[`g, `hdetect, `hunit]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_unit_rank_one #[`S, `L, `hline, `hcofixed, `K, `hstable, `hm, `hcard, `hbase, `hζ, `hp5, `hbad, `hclass, `hrank] #[`g, `hdetect, `hunit, `v, `P, `hsurj, `hns, `hval, `hzero]

end Note032CyclotomicPrimaryLogNonzeroDependencyAudit
