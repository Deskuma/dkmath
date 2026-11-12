/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerArithmetic

/-!
# 同じ非零ベクトルの整数化・Selmer 付値・類群捩れの依存監査

整数化で元の類を保つこと、実際の Selmer 条件、同じ主分数イデアルの指数、
条件付きの冪根と類群捩れ、元の Frey 不変量への到達を要求する。
全素点の所属や類群消滅を Frey 終点へ仮定として移していないことを確認する。
-/

namespace Note032CyclotomicKummerArithmeticDependencyAudit

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
-- Eight finite traversals inspect imported types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclicKummerIntegral.exists_integral_model
    #[``IsIntegral.exists_multiple_integral_of_isLocalization,
      ``IsIntegral.of_pow,
      ``DkMath.Lib.NumberTheory.CyclicKummerIntegral.rescale]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.exists_integral_model_same_vector
    #[``DkMath.Lib.NumberTheory.CyclicKummerIntegral.exists_integral_model,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.rescale_constantVector,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.rescale_constantClass]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmer.mem_valuationSpace_iff_selmer
    #[``IsDedekindDomain.selmerGroup,
      ``IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod,
      ``DkMath.Lib.NumberTheory.KummerSelmer.valuationSpace]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.constantVector_mem_valuationSpace_iff
    #[``DkMath.Lib.NumberTheory.KummerSelmer.count_span_eq_neg_valuation,
      ``DkMath.Lib.NumberTheory.DedekindFractionalValuation.count_spanSingleton,
      ``ZMod.intCast_zmod_eq_zero_iff_dvd]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmer.exists_fractionalIdeal_pow
    #[``FractionalIdeal.count_finprod,
      ``FractionalIdeal.finite_factors,
      ``FractionalIdeal.count_pow,
      ``DkMath.Lib.NumberTheory.DedekindFractionalValuation.ext_count]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmer.fractionalIdeal_pow_injective
    #[``FractionalIdeal.count_pow,
      ``DkMath.Lib.NumberTheory.DedekindFractionalValuation.ext_count]
  checkRoot ``DkMath.Lib.NumberTheory.KummerSelmer.exists_classGroup_torsion
    #[``DkMath.Lib.NumberTheory.KummerSelmer.exists_principal_fractionalIdeal_pow,
      ``ClassGroup.mk_eq_one_iff,
      ``DkMath.Lib.NumberTheory.KummerSelmer.mem_valuationSpace_mk_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residual_nonsplit_has_integral_weight_two_kummer_model
    #[``DkMath.FLT.Frey.Source.residual_nonsplit_has_weight_two_kummer_class,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.exists_integral_model_same_vector,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.rescale_constantVector,
      ``DkMath.Lib.NumberTheory.CyclicKummerIntegral.exists_integral_model,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerWeight.constantVector_weight_square]
  checkInputs ``DkMath.Lib.NumberTheory.CyclicKummerIntegral.exists_integral_model
    #[`P] #[`hinteger, `hden, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.exists_integral_model_same_vector
    #[`ψ, `hζ, `P] #[`hinteger, `hsame, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmer.mem_valuationSpace_iff_selmer
    #[`p, `x] #[`hunram, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic.constantVector_mem_valuationSpace_iff
    #[`ψ, `hζ, `P] #[`hSelmer, `hunram, `hdiv, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmer.exists_fractionalIdeal_pow
    #[`p, `hI, `hdiv] #[`hroot, `hclass, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmer.fractionalIdeal_pow_injective
    #[`hp, `hI, `hJ, `he] #[`hunique, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.KummerSelmer.exists_classGroup_torsion
    #[`p, `x, `hx] #[`hroot, `hfree, `hvanish, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_nonsplit_has_integral_weight_two_kummer_model
    #[`hp5, `hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hns]
    #[`P, `D, `hinteger, `hden, `hclass, `heigen, `hsame, `hSelmer, `hunram,
      `hx, `hdiv, `hweight, `hopen, `hsurj, `hzero, `hEXT, `hno]

end Note032CyclotomicKummerArithmeticDependencyAudit
