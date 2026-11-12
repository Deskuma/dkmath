/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerEquivariance

/-!
# 同じ Selmer 類の Galois 同変性と実際の類群二乗則の依存監査

型・コンストラクタ・opaque 証明本体を再帰走査し、実際の根の一意性、移送、
同変性、元の指標の二乗則を要求する。Frey の所属は明示入力に残す。
-/

namespace Note032CyclotomicKummerEquivarianceDependencyAudit

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
-- Ten finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.idealMap_span
    #[``FractionalIdeal.extended_spanSingleton,
      ``IsLocalization.map_unique]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classGroupEquiv
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classGroupMap_trans,
      ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classGroupMap_refl]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.map_mem
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.idealUnitsMap_principal,
      ``DkMath.Lib.NumberTheory.KummerSelmer.count_dvd_of_eq_pow]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.rootIdeal_map
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.idealUnitsMap_principal,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.idealUnits_pow_injective]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassGroup_equivariant
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.rootIdeal_map,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.classMapValue_eq]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassTorsion_equivariant
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassGroup_equivariant]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classImage_weight
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassTorsion_equivariant,
      ``DkMath.Lib.NumberTheory.KummerSelmerClassMap.toClassTorsion]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance.classGroupAction
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classGroupEquiv,
      ``NumberField.RingOfIntegers.mapRingEquiv]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance.classImage_weight_square
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classImage_weight,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantClass_weight_square]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_classImage_weight_square
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance.classImage_weight_square,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.rootIdeal_map
    #[`σ, `hp, `x, `hx] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassGroup_equivariant
    #[`σ, `p, `hp, `z] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassTorsion_equivariant
    #[`σ, `p, `hp, `z] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.classImage_weight
    #[`σ, `hp, `z, `a, `he] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance.classGroupAction
    #[] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance.classImage_weight_square
    #[`ψ, `hζ, `P, `hval, `hsurj, `hopen, `hweight, `γ] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_classImage_weight_square
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hsurj, `hval, `γ] #[`hno, `hCH, `hzero, `hvanish, `hequiv, `hclassMap, `hEXT]

end Note032CyclotomicKummerEquivarianceDependencyAudit
