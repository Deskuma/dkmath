/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerWeight

/-!
# 非自明な omega 二乗 Kummer 類の依存監査

元の指標と実際の根の比の因子化、二つの円分作用、同じ円分体への降下、
実際の持ち上げ、実際の商群・線形化と Frey 非分裂への到達を要求する。
-/

namespace Note032CyclotomicKummerWeightDependencyAudit

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

set_option maxHeartbeats 0 in
-- Seven finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.KummerRadicalCharacter.radicalCharacter
    #[``DkMath.Lib.NumberTheory.KummerRadicalCharacter.kernel_fixes_root,
      ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec]
  checkRoot ``DkMath.Lib.NumberTheory.KummerRadicalCharacter.conjugate_ratio
    #[``DkMath.Lib.NumberTheory.KummerRadicalCharacter.factor_apply,
      ``DkMath.Lib.NumberTheory.KummerRadicalCharacter.map_scalar,
      ``ZMod.map_smul,
      ``DkMath.Lib.NumberTheory.CyclotomicRootModule.cyclotomicCharacter_spec]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.presentationCharacter_kernel
    #[``DkMath.Lib.NumberTheory.CyclotomicCharacterKummer.character_eq_one_iff_fix_radical,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.fixingSubgroup_characterField]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.conjugate_radical_div_mem
    #[``DkMath.Lib.NumberTheory.KummerRadicalCharacter.conjugate_ratio,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.fixedField_kernel_eq,
      ``IntermediateField.mem_fixedField_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.base_constant_weight_square
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.conjugate_radical_div_mem,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.baseCharacter_lift,
      ``AlgEquiv.liftNormal_commutes]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantVector_weight_square
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantClass_weight_square,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.classLinearMap,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.kummerModule,
      ``QuotientGroup.map]
  checkRoot ``DkMath.FLT.Frey.Source.residual_nonsplit_has_weight_two_kummer_class
    #[``DkMath.FLT.Frey.Source.residual_nonsplit_has_kummer_presentation,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantClass_ne_one,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantVector_weight_square]
  checkInputs ``DkMath.Lib.NumberTheory.KummerRadicalCharacter.radicalCharacter
    #[`α, `hα, `hpow] #[`hpairing, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerRadicalCharacter.conjugate_ratio
    #[`ψ, `hsurj, `hker, `hweight, `σ, `u] #[`hsquare, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.presentationCharacter_kernel
    #[`ψ, `hζ, `P, `hopen] #[`hkernel, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.conjugate_radical_div_mem
    #[`ψ, `P, `hζ, `hsurj, `hopen, `hweight, `σ] #[`hfixed, `hdescent, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.base_constant_weight_square
    #[`ψ, `P, `hζ, `hsurj, `hopen, `hweight, `γ] #[`hlift, `hsquare, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantVector_weight_square
    #[`ψ, `P, `hζ, `hsurj, `hopen, `hweight, `γ] #[`hclass, `heigen, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_nonsplit_has_weight_two_kummer_class
    #[`hp5, `hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hns]
    #[`P, `hroot, `hgen, `hclass, `heigen, `hlift, `hweight, `hopen, `hsurj,
      `hzero, `hEXT, `hno]

end Note032CyclotomicKummerWeightDependencyAudit
