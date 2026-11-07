/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1Inflation
import DkMath.FLT.FreyFixedCoefficientSequence
import DkMath.FLT.FreyInvariantCosetObstruction
import DkMath.FLT.FreyFixedH1Connecting
import DkMath.FLT.FreyFixedH1PrimeOrder
#print "file: DkMathTest.FLT.Note032FreyConnectingDependencyAudit"

namespace Note032FreyConnectingDependencyAudit

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
-- Every new production declaration: checked types, constructors and opaque values.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInflationCoefficient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1Inflation #[``groupCohomology.map]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameClass_inflation #[``groupCohomology.H1π_comp_map_apply, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1Inflation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSubmodule #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedUpperQuotient]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficient_stable #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSubmodule]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficient #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficient_stable]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientProjection #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficient]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientInclusion, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientProjection]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence_shortExact #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence, ``Rep.mono_iff_injective, ``Rep.epi_iff_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetInvariant #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_ne_zero #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.no_invariant_lift #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence_shortExact, ``groupCohomology.δ]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetH0 #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetInvariant, ``groupCohomology.H0Iso]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoset_connecting #[``groupCohomology.δ₀_apply, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCocycle_include_value]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_values_killed #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.preimage, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.stable]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_inertia_class_killed #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_values_killed]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_tame_class_killed #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_values_killed]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_inertia_class_killed, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_tame_class_killed, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_connecting_prime_order_H1 #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_order_eq_prime, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoset_connecting, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameClass_inflation, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.no_invariant_lift]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedInflationCoefficient #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1Inflation #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficient_stable #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficient #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientProjection #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientSequence_shortExact #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting #[`T, `A] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameClass_inflation #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetInvariant #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetH0 #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoset_connecting #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `x] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_ne_zero #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.no_invariant_lift #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_values_killed #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_order_eq_prime #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_connecting_prime_order_H1 #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hshortExact, `hconnecting, `hH1, `horder, `hkilled, `hinflation, `hplacement, `hcontinuous, `hfinite]

end Note032FreyConnectingDependencyAudit
