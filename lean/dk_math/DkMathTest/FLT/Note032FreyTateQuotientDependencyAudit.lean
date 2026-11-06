/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateResonantWitness

#print "file: DkMathTest.FLT.Note032FreyTateQuotientDependencyAudit"

namespace Note032FreyTateQuotientDependencyAudit

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
-- Inspect checked types, constructors and opaque proof values.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.residualFiniteSecond #[]
  checkRoot ``DkMath.FLT.Frey.Source.residualFiniteSecond_surjective #[]
  checkRoot ``DkMath.FLT.Frey.Source.residualFiniteBasis_first #[``DkMath.FLT.Frey.Source.residualTateFiniteBasis]
  checkRoot ``DkMath.FLT.Frey.Source.residualFiniteSecond_eq_zero_iff #[``DkMath.FLT.Frey.Source.residualTateGenerators_generate, ``DkMath.FLT.Frey.Source.residualFiniteBasis_first]
  checkRoot ``DkMath.FLT.Frey.Source.residualFiniteQuotientEquiv #[``DkMath.FLT.Frey.Source.residualFiniteSecond_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualFiniteSecond_action #[``DkMath.FLT.Frey.Source.residualTate_matrix_reduction, ``DkMath.FLT.Frey.Source.residualTateActionMatrix_first_column]
  checkRoot ``DkMath.FLT.Frey.Source.residualFinite_absorption_iff #[``DkMath.FLT.Frey.Source.residualFiniteSecond_eq_zero_iff, ``DkMath.FLT.Frey.Source.residualFiniteSecond_action, ``DkMath.FLT.Frey.Source.residualFiniteSecond_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.residualFinite_inertia_absorption_iff #[``DkMath.FLT.Frey.Source.residualFinite_absorption_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residualSecond_frobenius_bound #[``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.torsion_index_le_finite_point_count_of_absorbing, ``DkMath.FLT.Frey.Source.residualFinite_absorption_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one_at #[``DkMath.FLT.Frey.Source.residualSecond_frobenius_bound]
  checkRoot ``DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one #[``DkMath.FLT.Frey.Source.goodReductionPointCount_pos, ``DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one_at]
  checkRoot ``DkMath.FLT.Frey.Source.residual_resonant_high_absorption_failure #[``DkMath.FLT.Frey.Source.residual_cofixed_point_count_tower_resonant_inertia_impossible]
  checkRoot ``DkMath.FLT.Frey.Source.residual_resonant_second_witness #[``DkMath.FLT.Frey.Source.residual_resonant_high_absorption_failure, ``DkMath.FLT.Frey.Source.residualFinite_absorption_iff]
  checkRoot ``DkMath.FLT.Frey.Source.residualSecond_nontrivial_resonant_inertia #[``DkMath.FLT.Frey.Source.exists_good_prime_ne, ``DkMath.FLT.Frey.Source.residual_resonant_second_witness]
  checkInputs ``DkMath.FLT.Frey.Source.residualFiniteSecond #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualFiniteQuotientEquiv #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualFiniteSecond_eq_zero_iff #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `x] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualFiniteSecond_action #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `σ, `x] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualFinite_absorption_iff #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `σ] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualFinite_inertia_absorption_iff #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `A] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualSecond_frobenius_bound #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `hq, `hqp, `hgood, `A, `hA, `hσ, `hd] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one_at #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hbound, `hq, `hqp, `hgood, `A, `hA, `hσ] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualSecond_frobenius_ne_one #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `hgood, `A, `hA, `hσ] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residual_resonant_high_absorption_failure #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hell, `hellp, `hgood] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residual_resonant_second_witness #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hell, `hellp, `hgood] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residualSecond_nontrivial_resonant_inertia #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hhigh, `hfixed, `hpointcount, `hCH, `htrivial, `hwitness]

end Note032FreyTateQuotientDependencyAudit
