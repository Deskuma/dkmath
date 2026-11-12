/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConditionalCofixedExclusion

#print "file: DkMathTest.FLT.Note032FreyTateUnipotenceDependencyAudit"

namespace Note032FreyTateUnipotenceDependencyAudit

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
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_product_zero #[``DkMath.Lib.NumberTheory.EllipticNodalInertia.inertia_difference_smooth, ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_square_zero #[``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_product_zero]
  checkRoot ``DkMath.FLT.Frey.Source.prime_power_inertia_difference_square_zero #[``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_square_zero, ``DkMath.FLT.Frey.Source.exists_geometry_at_bad_address, ``DkMath.Lib.NumberTheory.CyclotomicFrobenius.prime_power_valuation_eq_one]
  checkRoot ``DkMath.FLT.Frey.Source.tate_inertia_difference_square_zero #[``DkMath.FLT.Frey.Source.prime_power_inertia_difference_square_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateActionMatrix_inertia_square_zero #[``DkMath.FLT.Frey.Source.tate_inertia_difference_square_zero]
  checkRoot ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_inertia_eq_one #[``DkMath.FLT.Frey.Source.residualTateActionMatrix_inertia_square_zero, ``DkMath.FLT.Frey.Source.residualTateActionMatrix_first_column]
  checkRoot ``DkMath.FLT.Frey.Source.residualFinite_inertia_absorbs_at_bad #[``DkMath.FLT.Frey.Source.residualFinite_absorption_iff, ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_inertia_eq_one]
  checkRoot ``DkMath.FLT.Frey.Source.residual_not_cofixed_of_class_vanishing_and_resonant_absorption #[``DkMath.FLT.Frey.Source.residualSecond_nontrivial_resonant_inertia, ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_inertia_eq_one]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_failure #[``DkMath.FLT.Frey.Source.residual_not_cofixed_of_class_vanishing_and_resonant_absorption]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_counterexample #[``DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_failure, ``DkMath.FLT.Frey.Source.ResonantAbsorptionAt]
  checkRoot ``DkMath.FLT.Frey.Source.residual_hno_of_class_vanishing_and_resonant_absorption #[``DkMath.FLT.Frey.Source.residual_not_cofixed_of_class_vanishing_and_resonant_absorption]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_product_zero #[`E, `n, `A, `M, `hmodel, `C, `D, `hn, `σ, `τ, `hσ, `hτ] #[`hfix, `hsmooth, `hunipotent]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticNodalUnipotence.inertia_difference_square_zero #[`E, `n, `A, `M, `hmodel, `C, `D, `hn, `τ, `hτ] #[`hunipotent]
  checkInputs ``DkMath.FLT.Frey.Source.prime_power_inertia_difference_square_zero #[`S, `hp5, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ] #[`L, `hclass, `hbad, `hcofixed, `hbasis, `hunipotent]
  checkInputs ``DkMath.FLT.Frey.Source.tate_inertia_difference_square_zero #[`S, `hp5, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ] #[`L, `hclass, `hbad, `hcofixed, `hbasis, `hunipotent]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateActionMatrix_inertia_square_zero #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ] #[`hunipotent, `hhigh, `htrivial]
  checkInputs ``DkMath.FLT.Frey.Source.residualTateSecondCharacter_inertia_eq_one #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ] #[`hunipotent, `hhigh, `htrivial]
  checkInputs ``DkMath.FLT.Frey.Source.residualFinite_inertia_absorbs_at_bad #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ] #[`hunipotent, `hhigh, `htrivial]
  checkInputs ``DkMath.FLT.Frey.Source.residual_not_cofixed_of_class_vanishing_and_resonant_absorption #[`S, `L, `hline, `hζ, `hp5, `hclass, `hbad] #[`hcofixed, `hunipotent, `hhigh, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_failure #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hbadAll, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_counterexample #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hbadAll, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residual_hno_of_class_vanishing_and_resonant_absorption #[`S, `hζ, `hp5, `hclass, `hbadAll] #[`L, `hline, `hcofixed, `hbad, `hno, `hunipotent, `hhigh]

end Note032FreyTateUnipotenceDependencyAudit
