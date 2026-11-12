/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationWildNormality
import DkMath.FLT.FreyTameInertiaQuotient
import DkMath.Lib.Algebra.PrimeOrderResonance
import DkMath.FLT.FreyTameResonance
#print "file: DkMathTest.FLT.Note032FreyTameResonanceDependencyAudit"

namespace Note032FreyTameResonanceDependencyAudit

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
-- Traverse checked types, constructors and opaque values of every new production declaration.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.conjugate #[``DkMath.Lib.NumberTheory.ValuationTameCharacter.TameCharacter.apply_mem_nonunits_iff]
  checkRoot ``DkMath.Lib.NumberTheory.ValuationWildRigidity.inertiaWild_normal #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.conjugate]
  checkRoot ``DkMath.FLT.Frey.Source.wildInertiaSubgroup_normal #[``DkMath.Lib.NumberTheory.ValuationWildRigidity.inertiaWild_normal]
  checkRoot ``DkMath.FLT.Frey.Source.tameInertiaQuotient #[``DkMath.FLT.Frey.Source.wildInertiaSubgroup]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_character_kernel, ``QuotientGroup.lift]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_mk #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_range #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.tameInertia_frobenius_power #[``DkMath.FLT.Frey.Source.frobenius_conjugate_error_wild]
  checkRoot ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_self_iff #[``pow_inj_mod]
  checkRoot ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_inv #[``orderOf_dvd_iff_pow_eq_one]
  checkRoot ``DkMath.Lib.Algebra.PrimeOrderResonance.inv_ne_self #[``orderOf_dvd_of_pow_eq_one]
  checkRoot ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_ne_self_of_negative #[``DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_inv, ``DkMath.Lib.Algebra.PrimeOrderResonance.inv_ne_self]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_character_nontrivial #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_resonant_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_character_nontrivial, ``DkMath.FLT.Frey.Source.tameInertia_frobenius_power, ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_self_iff, ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_ne_self_of_negative, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.resonance]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_resonant_tame_character #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_resonant_profile]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationWildRigidity.IsWildAt.conjugate #[`A, `hσ, `hg] #[`hproq, `hfinite]
  checkInputs ``DkMath.Lib.NumberTheory.ValuationWildRigidity.inertiaWild_normal #[`A] #[`hproq, `hnormal]
  checkInputs ``DkMath.FLT.Frey.Source.wildInertiaSubgroup_normal #[`A] #[`S, `hnormal]
  checkInputs ``DkMath.FLT.Frey.Source.tameInertiaQuotient #[`A] #[`S, `hnormal]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_mk #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_continuous #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.tameDifferenceCharacter_range #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.tameInertia_frobenius_power #[`A, `hφ, `τ] #[`hwild, `hclass, `hbad, `hnormal]
  checkInputs ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_self_iff #[`hz] #[`hp, `hinvariant]
  checkInputs ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_eq_inv #[`hz, `hq] #[`hinvariant]
  checkInputs ``DkMath.Lib.Algebra.PrimeOrderResonance.pow_ne_self_of_negative #[`hp, `hz, `hq] #[`hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_character_nontrivial #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.tame_resonant_profile #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_resonant_tame_character #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hproq, `htrivial, `hplacement, `hcontinuous, `hfinite, `hfrob, `hwild, `hφ, `hinvariant]

end Note032FreyTameResonanceDependencyAudit
