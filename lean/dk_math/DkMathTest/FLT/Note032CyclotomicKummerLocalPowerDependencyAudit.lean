/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerLocalPower

#print "file: DkMathTest.FLT.Note032CyclotomicKummerLocalPowerDependencyAudit"

/-!
# 同じ完備化写像・根・定数・単元を保つ局所冪の依存監査

e=f=1 からの桁近似、完備化の稠密かつ閉じた像、同じ包含との可換性を要求する。
Frey の局所根には hbad 等を追加せず、最後の同じ単元との合流には元の算術入力を保持する。
-/

namespace Note032CyclotomicKummerLocalPowerDependencyAudit

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
-- Fifteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_integer_digit_of_inertiaDeg_eq_one
    #[``Ideal.inertiaDeg_eq_of_isMaximal,
      ``Algebra.finrank_eq_one_iff_bijective_algebraMap,
      ``IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_approximation_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_integer_digit_of_inertiaDeg_eq_one,
      ``IsDedekindDomain.HeightOneSpectrum.valuation_liesOver,
      ``IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_valuation_sub_lt_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_approximation_of_ef_eq_one,
      ``WithZero.exists_exp_neg_natCast_lt]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_algebraMap
    #[``UniformSpace.Completion.mapRingHom_coe]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_isUniformInducing_of_ramification_eq_one
    #[``UniformSpace.Completion.isUniformInducing_extension,
      ``IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.denseRange_valuedMap_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_valuation_sub_lt_of_ef_eq_one]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_denseRange_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.denseRange_valuedMap_of_ef_eq_one,
      ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_algebraMap]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_bijective_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_isUniformInducing_of_ramification_eq_one,
      ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_denseRange_of_ef_eq_one,
      ``IsUniformInducing.isComplete_range,
      ``IsComplete.isClosed]
  checkRoot ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.finrank_completion_eq_one_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_bijective_of_ef_eq_one,
      ``Algebra.finrank_eq_one_iff_bijective_algebraMap]
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalPower.exists_unit_pow_constant_of_ef_eq_one
    #[``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_bijective_of_ef_eq_one,
      ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_algebraMap,
      ``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.radical_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalPower.unit_pow_of_constant_pow
    #[``Units.val_div_eq_div_val,
      ``div_pow]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_local_radical_at_p
    #[``DkMath.FLT.Frey.Source.residual_kummer_ramification_and_inertiaDeg_eq_one_at_p,
      ``DkMath.Lib.NumberTheory.KummerLocalPower.exists_unit_pow_constant_of_ef_eq_one]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_constant_is_local_power_at_p
    #[``DkMath.FLT.Frey.Source.residual_kummer_local_radical_at_p,
      ``Ideal.exists_ideal_over_maximal_of_isIntegral]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_unit_is_local_power_at_p
    #[``DkMath.FLT.Frey.Source.residual_kummer_constant_is_local_power_at_p,
      ``DkMath.Lib.NumberTheory.KummerLocalPower.unit_pow_of_constant_pow]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_and_local_power
    #[``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_resonant_absorption,
      ``DkMath.FLT.Frey.Source.residual_kummer_unit_is_local_power_at_p]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_integer_digit_of_inertiaDeg_eq_one
    #[`v, `w, `hf, `x, `hx]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_approximation_of_ef_eq_one
    #[`v, `w, `he, `hf, `n, `x, `hx]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.exists_valuation_sub_lt_of_ef_eq_one
    #[`v, `w, `he, `hf, `x, `γ]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_algebraMap
    #[`v, `w, `a]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_isUniformInducing_of_ramification_eq_one
    #[`v, `w, `he]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.denseRange_valuedMap_of_ef_eq_one
    #[`v, `w, `he, `hf]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_denseRange_of_ef_eq_one
    #[`v, `w, `he, `hf]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.completionMap_bijective_of_ef_eq_one
    #[`v, `w, `he, `hf]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.NumberFieldCompletionComparison.finrank_completion_eq_one_of_ef_eq_one
    #[`v, `w, `he, `hf]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.KummerLocalPower.exists_unit_pow_constant_of_ef_eq_one
    #[`P, `v, `w, `hp, `he, `hf]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.Lib.NumberTheory.KummerLocalPower.unit_pow_of_constant_pow
    #[`φ, `c, `t, `hdecomp, `hpow]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_local_radical_at_p
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `vF, `w, `hvw]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero, `hbad, `hsurj, `hvanish, `he, `hf]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_constant_is_local_power_at_p
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `vF, `hpv]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero, `hbad, `hsurj, `hvanish, `he, `hf]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_unit_is_local_power_at_p
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `u, `c, `hdecomp, `vF, `hpv]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero, `hbad, `hsurj, `hvanish, `he, `hf]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_and_local_power
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `hbad, `hsurj, `hvanish]
    #[`hno, `hCH, `hEXT, `hlocalDegree, `hcompletion, `hrootProvider, `hlocalPower, `hval, `hzero]

end Note032CyclotomicKummerLocalPowerDependencyAudit
