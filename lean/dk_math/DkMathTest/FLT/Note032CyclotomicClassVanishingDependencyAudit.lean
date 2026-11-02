/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicClassVanishing

#print "file: DkMathTest.FLT.Note032CyclotomicClassVanishingDependencyAudit"

/-!
# 同じ類群の冪商から捩れへの消滅移送の依存監査

Fitting 分解、有限性による全射から単射、重み付き和の固有性と整数持ち上げ、
実際の類群の有限性と円分群位数を要求する。商の算術的消滅は公開型に残す。
-/

namespace Note032CyclotomicClassVanishingDependencyAudit

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

private def checkTypeConstants (root : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := info.type.getUsedConstants
  for n in required do
    unless names.contains n do throwError "Required type guard absent in {root}: {n}"
  logInfo m!"PASS guards: {root}; finite and coefficient hypotheses present."

set_option maxHeartbeats 0 in
-- Eleven finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_kernel_eq_zero
    #[``LinearMap.eventually_isCompl_ker_pow_range_pow,
      ``Finite.injective_iff_surjective]
  checkRoot ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.weightedSum_eigen
    #[``Fintype.sum_bijective]
  checkRoot ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.liftedWeightedSum_quotient
    #[``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.quotientAction,
      ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.weightedSum,
      ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.liftedWeightedSum]
  checkRoot ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.liftedWeightedSum_torsion
    #[``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsionModule,
      ``ZMod.natCast_zmod_val]
  checkRoot ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_eigen_eq_zero
    #[``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_kernel_eq_zero,
      ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.weightedSum_eigen,
      ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.liftedWeightedSum_quotient,
      ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.liftedWeightedSum_torsion]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classTorsion_eq_one_of_quotient_eigen_vanishing
    #[``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_eigen_eq_zero,
      ``NumberField.RingOfIntegers.instFintypeClassGroup]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card
    #[``IsGalois.card_aut_eq_finrank,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.rootField_finrank]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card_isUnit
    #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card,
      ``ZMod.isUnit_iff_coprime]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classImage_eq_one_of_quotient_weight_square_vanishing
    #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classTorsion_eq_one_of_quotient_eigen_vanishing,
      ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card_isUnit,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance.classImage_weight_square]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_classImage_eq_one_of_quotient_vanishing
    #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classImage_eq_one_of_quotient_weight_square_vanishing,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_quotient_vanishing
    #[``DkMath.FLT.Frey.Source.residual_kummer_classImage_eq_one_of_quotient_vanishing,
      ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square]
  checkInputs ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_kernel_eq_zero
    #[`p, `f, `hmod, `x, `hpx, `hfx] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkInputs ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_eigen_eq_zero
    #[`ρ, `χ, `hcard, `hvanish, `x, `hpx, `he] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classTorsion_eq_one_of_quotient_eigen_vanishing
    #[`χ, `hcard, `hvanish, `c, `he] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.root_galois_card_isUnit
    #[`hζ] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classImage_eq_one_of_quotient_weight_square_vanishing
    #[`hζ, `ψ, `P, `hval, `hsurj, `hopen, `hweight, `hvanish] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_classImage_eq_one_of_quotient_vanishing
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hsurj, `hval, `hvanish] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_quotient_vanishing
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hsurj, `hval, `hvanish] #[`hno, `hCH, `hzero, `hinjective, `hquotInjective, `hfiniteClass, `hcardUnit, `hEXT]
  checkTypeConstants ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_kernel_eq_zero #[``Finite]
  checkTypeConstants ``DkMath.Lib.Algebra.FiniteEigenTorsionBridge.torsion_eigen_eq_zero #[``Finite, ``Fintype, ``NeZero, ``IsUnit]

end Note032CyclotomicClassVanishingDependencyAudit
