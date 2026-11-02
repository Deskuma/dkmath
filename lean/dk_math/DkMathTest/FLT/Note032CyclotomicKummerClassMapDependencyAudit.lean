/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerClassMap

/-!
# Selmer 類群写像・完全列・同じ単元への復帰の依存監査

実際の主分数イデアルの冪根、代表元独立性、積、単元核、全射性と線形化を要求する。
Frey の受け口は明示的に Selmer 所属と類群像の零化を条件に保ち、hno 閉包とは区別する。
-/

namespace Note032CyclotomicKummerClassMapDependencyAudit

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
-- Nine finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.rootClass_independent
    #[``DkMath.Lib.NumberTheory.KummerSelmerClassMap.rootIdeal_change_representative,
      ``DkMath.Lib.NumberTheory.KummerSelmer.fractionalIdeal_pow_injective,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.principal_class_eq_one]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassGroup
    #[``DkMath.Lib.NumberTheory.KummerSelmerClassMap.rootClass_independent,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.rootIdeal_mul,
      ``DkMath.Lib.NumberTheory.KummerSelmer.exists_principal_fractionalIdeal_pow]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassTorsionLinear
    #[``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassGroup,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.classTorsionModule,
      ``AddMonoidHom.toZModLinearMap]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerExact.short_exact
    #[``DkMath.Lib.NumberTheory.KummerSelmerExact.unitInclusion_injective,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.kernel_eq_unit_range,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.toClassTorsion_surjective,
      ``IsDedekindDomain.selmerGroup.fromUnit_ker]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerExact.kernel_eq_unit_range
    #[``DkMath.Lib.NumberTheory.KummerSelmerExact.toClassGroup_eq_one_iff_unit,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.principal_of_class_eq_one,
      ``FractionalIdeal.spanSingleton_eq_spanSingleton]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerExact.toClassTorsion_surjective
    #[``ClassGroup.induction,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.principal_of_class_eq_one,
      ``DkMath.Lib.NumberTheory.KummerSelmer.count_dvd_of_eq_pow,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.idealUnits_pow_injective]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.rescale_classImage
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.rescale_constantClass,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassTorsion]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.unit_of_classImage_eq_one
    #[``DkMath.Lib.NumberTheory.KummerSelmerExact.unit_decomposition,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.toClassGroup_eq_one_iff_unit,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantClass_ne_one]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_unit_of_classImage_eq_one
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.unit_of_classImage_eq_one,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.classImage,
      ``DkMath.FLT.Frey.Source.residualCyclicExtensionCharacter]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.rootClass_independent
    #[`hp, `x, `y, `hx, `hy, `he] #[`hclass, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassGroup
    #[`p, `hp] #[`hmap, `hchoice, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassTorsionLinear
    #[`p, `hp] #[`hlinear, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerExact.short_exact
    #[`p, `hp] #[`hinj, `hexact, `hsurj, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerExact.kernel_eq_unit_range
    #[`p, `hp] #[`hunit, `hexact, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerExact.toClassTorsion_surjective
    #[`p, `hp] #[`hsurj, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.rescale_classImage
    #[`ψ, `hζ, `P, `hval, `c, `hc] #[`hsame, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.unit_of_classImage_eq_one
    #[`ψ, `hζ, `P, `hval, `hzero] #[`hunit, `hu, `hvanish, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_unit_of_classImage_eq_one
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hval, `hzero]
    #[`hunit, `hu, `hfree, `hvanish, `hEXT, `hno]

end Note032CyclotomicKummerClassMapDependencyAudit
