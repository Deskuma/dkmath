/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerUnitEquivariance

/-!
# 同変な短完全列と、同じ非零 ω² 単元類への還元の依存監査

型・コンストラクタ・opaque 証明本体を走査し、実際の単元写像の同変性と
単射性、同じ単元逆像の一意性、元の二乗則と Frey 指標の共役則を要求する。
所属と類群像の零化を公開型の明示入力に残す。
-/

namespace Note032CyclotomicKummerUnitEquivarianceDependencyAudit

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
-- Twelve finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClassEquiv
    #[``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClassMap_trans,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClassMap_refl]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.selmerEquiv
    #[``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.selmerMap_trans,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.selmerMap_refl]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitInclusion_equivariant
    #[``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.commutes]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.short_exact_equivariant
    #[``DkMath.Lib.NumberTheory.KummerSelmerExact.short_exact,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitInclusion_equivariant,
      ``DkMath.Lib.NumberTheory.KummerSelmerEquivariance.CompatibleAut.toClassTorsion_equivariant]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.existsUnique_unitClass
    #[``DkMath.Lib.NumberTheory.KummerSelmerExact.kernel_eq_unit_range,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.unitInclusion_injective]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitPreimage_equivariant
    #[``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitPreimage_eq,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitInclusion_equivariant]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClassLinearMap_weight
    #[``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClass_weight,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.unitInclusion_injective,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitInclusion_equivariant]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.numberField_short_exact_equivariant
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unitClassAction,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.selmerAction,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.classTorsionAction,
      ``DkMath.Lib.NumberTheory.KummerSelmerExact.toClassTorsion_surjective]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unitImage_ne_one
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantClass_ne_one,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitPreimage_ne_one]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unitImage_weight_square
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantClass_weight_square,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClassLinearMap_weight]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unit_of_classImage_eq_one_weight_square
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerClassMap.unit_of_classImage_eq_one,
      ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitPreimage_eq,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unitImage_weight_square]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unit_of_classImage_eq_one_weight_square,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen,
      ``DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitInclusion_equivariant
    #[`p, `hp, `σ, `u] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.short_exact_equivariant
    #[`p, `hp, `σ] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitPreimage_equivariant
    #[`p, `hp, `σ, `z, `hzero] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance.unitClassLinearMap_weight
    #[`p, `hp, `σ, `z, `u, `hu, `a, `he] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.numberField_short_exact_equivariant
    #[`p, `hp] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unitImage_ne_one
    #[`ψ, `hζ, `P, `hval, `hzero] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unitImage_weight_square
    #[`ψ, `hζ, `P, `hval, `hzero, `hsurj, `hopen, `hweight, `γ] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance.unit_of_classImage_eq_one_weight_square
    #[`ψ, `hζ, `P, `hval, `hzero, `hsurj, `hopen, `hweight] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hsurj, `hval, `hzero] #[`hno, `hCH, `hvanish, `hequiv, `hunitWeight, `hunit, `hEXT]

end Note032CyclotomicKummerUnitEquivarianceDependencyAudit
