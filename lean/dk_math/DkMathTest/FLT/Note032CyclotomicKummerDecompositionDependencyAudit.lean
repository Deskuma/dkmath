/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerDecomposition

#print "file: DkMathTest.FLT.Note032CyclotomicKummerDecompositionDependencyAudit"

/-!
# 同じ Frey Kummer 根の有限分解群に対する再帰依存監査

実際の絶対分解群持ち上げ、有限体への制限、生成性、慣性位数と剰余次数の公式を要求する。
p 上の Frey 公開入口に hbad・hval・hzero・hvanish・hsurj や局所次数 provider を加えない。
-/

namespace Note032CyclotomicKummerDecompositionDependencyAudit

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
-- Eleven finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_lift_mem_integral_decomposition
    #[``AlgEquiv.restrictNormalHom_surjective,
      ``Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite,
      ``Ideal.exists_ideal_over_maximal_of_isIntegral]
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_valuation_decomposition_of_integral_stabilizer
    #[``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction,
      ``Ideal.image_subset_nonunits_valuationSubring]
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_lift_mem_valuation_decomposition
    #[``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_lift_mem_integral_decomposition,
      ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_valuation_decomposition_of_integral_stabilizer]
  checkRoot ``DkMath.Lib.NumberTheory.KummerDecomposition.subgroup_eq_bot_of_fixes_radical
    #[``DkMath.Lib.NumberTheory.CyclicKummer.Presentation.algHom_ext]
  checkRoot ``DkMath.Lib.NumberTheory.KummerDecomposition.ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
    #[``DkMath.Lib.NumberTheory.KummerDecomposition.subgroup_eq_bot_of_fixes_radical,
      ``Ideal.card_stabilizer_eq_card_inertia_mul_finrank,
      ``DkMath.Lib.NumberTheory.KummerLocalValuation.ramification_eq_one_of_inertia_fixes_radical]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p
    #[``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_lift_mem_valuation_decomposition,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.character_eq_one_iff_fix_root,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.kernelEquiv_mem_decomposition_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_eq_bot_at_p
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p,
      ``DkMath.Lib.NumberTheory.KummerDecomposition.subgroup_eq_bot_of_fixes_radical]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.ramification_and_inertiaDeg_eq_one_at_p
    #[``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p,
      ``DkMath.Lib.NumberTheory.KummerDecomposition.ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_finite_decomposition_fixes_radical_at_p
    #[``DkMath.FLT.Frey.Source.residual_kummer_radical_decomposition_fixed_at_p,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p,
      ``DkMath.Lib.NumberTheory.CyclotomicCharacterField.characterField_numberField]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_decomposition_eq_bot_at_p
    #[``DkMath.FLT.Frey.Source.residual_kummer_finite_decomposition_fixes_radical_at_p,
      ``DkMath.Lib.NumberTheory.KummerDecomposition.subgroup_eq_bot_of_fixes_radical]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_ramification_and_inertiaDeg_eq_one_at_p
    #[``DkMath.FLT.Frey.Source.residual_kummer_radical_decomposition_fixed_at_p,
      ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.ramification_and_inertiaDeg_eq_one_at_p]
  checkInputs ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_lift_mem_integral_decomposition
    #[`L, `Q, `hqQ, `τ, `hτ]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_valuation_decomposition_of_integral_stabilizer
    #[`𝔔, `hq, `hq𝔔, `σ, `hσ]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.AbsoluteDecompositionLift.exists_lift_mem_valuation_decomposition
    #[`L, `Q, `hq, `hqQ, `τ, `hτ]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.KummerDecomposition.subgroup_eq_bot_of_fixes_radical
    #[`P, `H, `hfix]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.KummerDecomposition.ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
    #[`P, `v, `w, `hfix]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p
    #[`ψ, `hζ, `hopen, `hweight, `P, `hlocal, `w, `hpw, `τ, `hτ]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.finite_decomposition_eq_bot_at_p
    #[`ψ, `hζ, `hopen, `hweight, `P, `hlocal, `w, `hpw]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition.ramification_and_inertiaDeg_eq_one_at_p
    #[`ψ, `hζ, `hopen, `hweight, `P, `hlocal, `v, `w, `hvw, `hpv]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_finite_decomposition_fixes_radical_at_p
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_decomposition_eq_bot_at_p
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_ramification_and_inertiaDeg_eq_one_at_p
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `v, `P, `hp5]
    #[`hno, `hCH, `hval, `hzero, `hunramified, `hfiniteInertia, `hfiniteDecomposition, `hSelmer, `hEXT, `hlocalDegree, `hcompletion, `hbad, `hvanish, `hsurj]

end Note032CyclotomicKummerDecompositionDependencyAudit
