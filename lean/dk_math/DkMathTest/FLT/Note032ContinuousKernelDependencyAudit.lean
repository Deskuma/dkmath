/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicWeightTwoTarget
import DkMath.FLT.FreyContinuousObstructionCertificate

#print "file: DkMathTest.FLT.Note032ContinuousKernelDependencyAudit"

namespace Note032ContinuousKernelDependencyAudit

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
-- Recursively inspect all new definitions, types, proof values and constructors.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.weightTwoComponent #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.classModPAction]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.weightTwo_eq_bot_iff #[]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.bernoulli_two_numerator #[]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.prime_not_dvd_bernoulli_two_numerator #[``DkMath.Lib.NumberTheory.CyclotomicClassVanishing.bernoulli_two_numerator]
  checkRoot ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.cocycle #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.cocycle_continuous #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_evaluate #[]
  checkRoot ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_injective #[``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_evaluate]
  checkRoot ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_ne_zero #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_apply #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_forget #[``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_evaluate]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_continuous #[``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.cocycle_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_eq #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_coset]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingClass_eq_delta #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_eq, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoset_connecting]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter_mk #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCocycle_mk #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameClass_inflation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass_inflation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_injective]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.cyclic_balanced_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_balanced_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_card_dvd_fixed_of_radical_generator]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.stage_zero_card_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.cyclic_balanced_profile]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.stage_one_card_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.cyclic_balanced_profile]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_kernel_detected #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_forget, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameClass_inflation, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_class_nonzero #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_kernel_detected, ``DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_ne_zero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_apply #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_injective #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_forget #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_continuous #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_eq #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingClass_eq_delta #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter_mk #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCocycle_mk #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameClass_inflation #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter_injective #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.cyclic_balanced_profile #[`h, `hp5] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.stage_zero_card_profile #[`h, `hp5] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.stage_one_card_profile #[`h, `hp5] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_kernel_detected #[`h, `hp5] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_class_nonzero #[`h, `hp5] #[`hdiv, `hidx, `hstab, `hres, `hroot, `halg, `hhenselian, `hclass, `hcofixed, `hcompare, `hcyclic, `htail, `hgen, `hfinite, `hcontinuous, `hopen, `hcontain, `hprimitive, `hreflection, `hherbrand, `hvanish]

end Note032ContinuousKernelDependencyAudit
