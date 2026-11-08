/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalGeneratorCertificate

#print "file: DkMathTest.FLT.Note032FreyRadicalDependencyAudit"

namespace Note032FreyRadicalDependencyAudit

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
-- Traverse checked types, constructors and opaque values for all thirty-one roots.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower #[``IsAlgClosed.exists_pow_nat_eq]
  checkRoot ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_zero #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower]
  checkRoot ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_succ_pow #[``IsAlgClosed.exists_pow_nat_eq, ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower]
  checkRoot ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_compat #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_succ_pow]
  checkRoot ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_pow #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_compat]
  checkRoot ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_ne_zero #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_pow]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.radical #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.ratio #[``DkMath.Lib.NumberTheory.InertiaRadical.radical]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.radical_ne_zero #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_pow #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_pow]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_compat #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_compat]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_eq_one_iff #[``DkMath.Lib.NumberTheory.InertiaRadical.radical_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.valuation_prime_eq_one #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.inertia_fixes_primePower_root #[``DkMath.Lib.NumberTheory.ValuationInertiaPower.inertia_fixed_of_pow_eq_one, ``DkMath.Lib.NumberTheory.InertiaRadical.valuation_prime_eq_one]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character #[``DkMath.Lib.NumberTheory.InertiaRadical.inertia_fixes_primePower_root, ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_pow]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character_val #[``DkMath.Lib.NumberTheory.InertiaRadical.character]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character_pow #[``DkMath.Lib.NumberTheory.InertiaRadical.ratio_pow]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character_compat #[``DkMath.Lib.NumberTheory.InertiaRadical.ratio_compat]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.exists_primitive_generator #[``DkMath.Lib.NumberTheory.KummerInertia.exists_inertia_ne_of_pow_eq, ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_compat, ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_succ_pow, ``orderOf_eq_prime_pow]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.generator #[``DkMath.Lib.NumberTheory.InertiaRadical.exists_primitive_generator]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive #[``DkMath.Lib.NumberTheory.InertiaRadical.exists_primitive_generator]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed #[``DkMath.Lib.NumberTheory.InertiaRadical.ratio_eq_one_iff]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.image_eq_pow_of_primitive #[``IsPrimitiveRoot.eq_pow_of_pow_eq_one, ``DkMath.Lib.NumberTheory.InertiaRadical.character_pow]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive #[``DkMath.Lib.NumberTheory.InertiaRadical.image_eq_pow_of_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.range_eq_zpowers_of_primitive #[``DkMath.Lib.NumberTheory.InertiaRadical.image_eq_pow_of_primitive]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_card_of_primitive #[``DkMath.Lib.NumberTheory.InertiaRadical.range_eq_zpowers_of_primitive, ``QuotientGroup.quotientKerEquivRange]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_isCyclic_of_primitive #[``DkMath.Lib.NumberTheory.InertiaRadical.range_eq_zpowers_of_primitive]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaRadical.exists_generator_corrections #[``DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_card_of_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_isCyclic_of_primitive]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_generator_stage_correction #[``DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.radical_generator_error #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_generator_stage_correction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_radical_generator_error #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_card_of_primitive, ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_isCyclic_of_primitive, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.radical_generator_error]
  checkInputs ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower #[`p, `hp, `a] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hq, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_zero #[`p, `hp, `a] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hq, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_succ_pow #[`p, `hp, `a] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hq, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_compat #[`p, `hp, `a] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hq, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_pow #[`p, `hp, `a] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hq, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_ne_zero #[`p, `hp, `a] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hq, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.radical #[`hp] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive, `hq]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.ratio #[`hp] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive, `hq]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.radical_ne_zero #[`hp, `hq] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_pow #[`hp, `hq] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_compat #[`hp] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive, `hq]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.ratio_eq_one_iff #[`hp, `hq] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hpq, `A, `hA, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.valuation_prime_eq_one #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.inertia_fixes_primePower_root #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character_val #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character_pow #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character_compat #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.exists_primitive_generator #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.generator #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.generator_primitive #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.image_eq_pow_of_primitive #[`hp, `hq, `hpq, `A, `hA, `hprimitive] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.correction_of_primitive #[`hp, `hq, `hpq, `A, `hA, `hprimitive] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.range_eq_zpowers_of_primitive #[`hp, `hq, `hpq, `A, `hA, `hprimitive] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_card_of_primitive #[`hp, `hq, `hpq, `A, `hA, `hprimitive] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.quotient_isCyclic_of_primitive #[`hp, `hq, `hpq, `A, `hA, `hprimitive] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaRadical.exists_generator_corrections #[`hp, `hq, `hpq, `A, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_generator_stage_correction #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.radical_generator_error #[`h, `hp5] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hclass, `hcofixed, `hprimitive]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_radical_generator_error #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hprimitive]

end Note032FreyRadicalDependencyAudit
