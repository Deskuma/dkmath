/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerSelmer

#print "file: DkMathTest.FLT.Note032CyclotomicKummerSelmerDependencyAudit"

/-!
# 同じ根の局所固定性から元の Frey Selmer 所属への依存監査

実際の分岐指数・付値比較、慣性位数、同じ根の生成性、既存の絶対慣性持ち上げ、
全素点の指数判定と p 上・p 外の元の局所固定性を要求する。
hbad と hp5 は公開型に保ち、hval と hzero を新しい入口から内部導出する。
-/

namespace Note032CyclotomicKummerSelmerDependencyAudit

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
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalValuation.log_pow_eq_ramification_mul
    #[``IsDedekindDomain.HeightOneSpectrum.valuation_liesOver]
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalValuation.count_dvd_of_ramification_eq_one
    #[``DkMath.Lib.NumberTheory.KummerLocalValuation.log_pow_eq_ramification_mul,
      ``DkMath.Lib.NumberTheory.DedekindFractionalValuation.count_spanSingleton]
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalValuation.ramification_eq_one_of_inertia_fixes_radical
    #[``Ideal.card_inertia_eq_ramificationIdxIn,
      ``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.algHom_ext]
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalValuation.count_dvd_of_inertia_fixes_radical
    #[``DkMath.Lib.NumberTheory.KummerLocalValuation.count_dvd_of_ramification_eq_one,
      ``DkMath.Lib.NumberTheory.KummerLocalValuation.ramification_eq_one_of_inertia_fixes_radical]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerSelmer.finite_inertia_fixes_radical
    #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.character_eq_one_iff_fix_root,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_inertia_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerSelmer.constantVector_mem_valuationSpace_of_absolute_inertia
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerSelmer.finite_inertia_fixes_radical,
      ``DkMath.Lib.NumberTheory.KummerLocalValuation.count_dvd_of_inertia_fixes_radical,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.characterField_numberField,
      ``Ideal.exists_ideal_over_maximal_of_isIntegral,
      ``DkMath.Lib.NumberTheory.KummerSelmer.mem_valuationSpace_mk_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_mem_valuationSpace
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerSelmer.constantVector_mem_valuationSpace_of_absolute_inertia,
      ``DkMath.FLT.Frey.Source.residual_kummer_radical_decomposition_fixed_at_p,
      ``DkMath.FLT.Frey.Source.residual_kummer_radical_inertia_fixed_away]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_mem_selmer
    #[``DkMath.FLT.Frey.Source.residual_kummer_mem_valuationSpace,
      ``DkMath.Lib.NumberTheory.KummerSelmer.mem_valuationSpace_iff_selmer]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_resonant_absorption
    #[``DkMath.FLT.Frey.Source.residual_kummer_mem_valuationSpace,
      ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_quotient_vanishing]
  checkInputs ``DkMath.Lib.NumberTheory.KummerLocalValuation.log_pow_eq_ramification_mul
    #[`v, `w, `p, `α, `b, `hpow] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerLocalValuation.count_dvd_of_ramification_eq_one
    #[`v, `w, `p, `α, `b, `hpow, `he] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.KummerLocalValuation.ramification_eq_one_of_inertia_fixes_radical
    #[`P, `v, `w, `hfix] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerSelmer.finite_inertia_fixes_radical
    #[`ψ, `hζ, `hopen, `hweight, `P, `hlocal, `w, `τ, `hτ] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerSelmer.constantVector_mem_valuationSpace_of_absolute_inertia
    #[`ψ, `hζ, `hopen, `hweight, `P, `hlocal] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_mem_valuationSpace
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `hbad] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_mem_selmer
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `hbad] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_resonant_absorption
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5, `hbad, `hsurj, `hvanish] #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hSelmer, `hEXT]

end Note032CyclotomicKummerSelmerDependencyAudit
