/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicUnitSplit

#print "file: DkMathTest.FLT.Note032CyclotomicUnitClosureDependencyAudit"

namespace Note032CyclotomicUnitClosureDependencyAudit

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
-- Twelve finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.symm_symm_apply_zeta #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.characterEquiv_symm_root]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.smul_infinitePlace_eq_self_iff #[``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.symm_symm_apply_zeta, ``NumberField.InfinitePlace.mk_eq_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.card_fixedPlaces_prime #[``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.smul_infinitePlace_eq_self_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.sum_inv_sq_mul_sub_one #[``FiniteField.sum_pow_units]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.sum_inv_sq_mul_indicator #[]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_unitAction #[``DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace.trace_unitAction_eq_character_add_fixedPlaces, ``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.card_fixedPlaces_prime]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.omegaSquareProjector_eq_units_sum #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector.omegaSquareProjector_apply_units]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_omegaSquareProjector #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_unitAction, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.sum_inv_sq_mul_sub_one, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.sum_inv_sq_mul_indicator]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.weightSquareSpace_finrank_eq_one #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_omegaSquareProjector, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank.weightSquareSpace_finrank_eq_one_of_trace]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_omegaSquareProjector, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero.primaryLog_projectedCyclotomicUnit_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.exists_global_unit_pow_of_primary #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.primaryWeightSquareSpace_eq_bot_iff_global_power]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_class_vanishing #[``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot, ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.smul_infinitePlace_eq_self_iff #[`hζ, `_hp, `d, `w] #[`hfixed, `htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed.card_fixedPlaces_prime #[`hζ, `hp, `d] #[`hfixed, `htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_unitAction #[`hζ, `hp5, `d] #[`hfixed, `htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.trace_omegaSquareProjector #[`hζ, `hp5] #[`hfixed, `htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.weightSquareSpace_finrank_eq_one #[`hζ, `hp5] #[`htrace, `hrank, `hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot #[`hζ, `hp5] #[`htrace, `hrank, `hunit, `g, `hdetect]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.exists_global_unit_pow_of_primary #[`hζ, `hp5, `u, `hu] #[`htrace, `hrank, `hunit]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_class_vanishing #[`S, `L, `hline, `hcofixed, `K, `hstable, `hm, `hcard, `hbase, `hζ, `hp5, `hbad, `hclass] #[`htrace, `hrank, `hunit, `g, `hdetect, `hfixed, `v, `P, `hsurj, `hns]

end Note032CyclotomicUnitClosureDependencyAudit
