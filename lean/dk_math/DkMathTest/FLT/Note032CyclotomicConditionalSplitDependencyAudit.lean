/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalSplit

#print "file: DkMathTest.FLT.Note032CyclotomicConditionalSplitDependencyAudit"

/-!
# 実際の局所冪核・3次合同・算術仮定付き非分裂排除の依存監査

同じ局所根からの3次合同と、同じ単元の部分空間所属を要求する。
最終の非分裂排除・安定補空間では v,P,hsurj を内部供給し、hbad,hclass,hunit を保持する。
-/

namespace Note032CyclotomicConditionalSplitDependencyAudit

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
-- Thirteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit.pow_sub_one_mem_cube_of_local_pow
    #[``add_pow_prime_eq,
      ``IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ``IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.classMapAlong_mk_eq_one_iff
    #[``QuotientGroup.eq_one_iff]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_localPowerSpace_iff
    #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.localClassMap_mk_eq_one_iff,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.localPowerSpace]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_primaryWeightSquareSpace_iff
    #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_localPowerSpace_iff,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.primaryWeightSquareSpace]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.primaryWeightSquareSpace_eq_bot_iff_global_power
    #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.unitClass_eq_one_of_space_eq_bot,
      ``QuotientGroup.mk'_surjective]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.natCast_mem_ramifiedIdeal_pow
    #[``IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.ramified_residue_card
    #[``IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.unit_pow_sub_one_mem_ramifiedIdeal
    #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.ramified_residue_card,
      ``FiniteField.pow_card_sub_one_eq_one]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.pow_sub_one_mem_ramifiedIdeal_cube_of_local_power
    #[``DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit.pow_sub_one_mem_cube_of_local_pow,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.natCast_mem_ramifiedIdeal_pow,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.unit_pow_sub_one_mem_ramifiedIdeal,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_localPowerSpace_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_primary_unit_witness
    #[``DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_and_local_power,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_primaryWeightSquareSpace_iff,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.pow_sub_one_mem_ramifiedIdeal_cube_of_local_power,
      ``DkMath.Lib.NumberTheory.CyclotomicKernelField.rootField_isCyclotomic]
  checkRoot ``DkMath.FLT.Frey.Source.residual_kummer_impossible_of_primary_unit_vanishing
    #[``DkMath.FLT.Frey.Source.residual_kummer_primary_unit_witness,
      ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.unitClass_eq_one_of_space_eq_bot]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_impossible
    #[``DkMath.FLT.Frey.Source.residual_nonsplit_has_kummer_presentation,
      ``DkMath.FLT.Frey.Source.residual_kummer_impossible_of_primary_unit_vanishing]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement
    #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_impossible,
      ``DkMath.FLT.Frey.Source.residual_nonsplit_has_kummer_presentation]
  checkInputs ``DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit.pow_sub_one_mem_cube_of_local_pow
    #[`hp, `hp5, `𝔭, `u, `hz1, `hp2, `hloc]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.classMapAlong_mk_eq_one_iff
    #[`p, `φ, `u]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_localPowerSpace_iff
    #[`p, `u]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.mk_mem_primaryWeightSquareSpace_iff
    #[`hζ, `u]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace.primaryWeightSquareSpace_eq_bot_iff_global_power
    #[`hζ]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.natCast_mem_ramifiedIdeal_pow
    #[`hζ, `n, `hn]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.ramified_residue_card
    #[`hζ]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.unit_pow_sub_one_mem_ramifiedIdeal
    #[`hζ, `u]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.pow_sub_one_mem_ramifiedIdeal_cube_of_local_power
    #[`hζ, `hp5, `u, `hloc]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne, `hz1, `hp2]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_primary_unit_witness
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hp5, `hbad, `hclass, `v, `P, `hsurj]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne, `hunit]
  checkInputs ``DkMath.FLT.Frey.Source.residual_kummer_impossible_of_primary_unit_vanishing
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hp5, `hbad, `hclass, `v, `P, `hsurj, `hunit]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_impossible
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hp5, `hbad, `hclass, `hunit, `hns]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne, `v, `P, `hsurj]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement
    #[`hline, `hcofixed, `hstable, `hm, `hcard, `hbase, `hζ, `hp5, `hbad, `hclass, `hunit]
    #[`hno, `hCH, `hEXT, `hval, `hzero, `hlocalDegree, `hrootProvider, `hLambda, `hfinrankOne, `v, `P, `hsurj, `hns]

end Note032CyclotomicConditionalSplitDependencyAudit
