/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedQuotientTrivial
import DkMath.FLT.FreyFixedConnectingInjective
import DkMath.FLT.FreyFixedConnectingKernel
import DkMath.FLT.FreyConnectingKernelPrimeOrder
import DkMath.FLT.FreyConnectingKernelCertificate
#print "file: DkMathTest.FLT.Note032FreyKernelDependencyAudit"

namespace Note032FreyKernelDependencyAudit

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
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_all_invariant #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetInvariant]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_action_trivial #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_all_invariant]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientInvariantEquiv #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_all_invariant]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH0Projection #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH0Projection_zero #[``groupCohomology.map_id_comp_H0Iso_hom_apply]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH0Projection_zero, ``groupCohomology.mapShortComplex₃_exact]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1CoefficientMap #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoefficientInclusion]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1CoefficientKernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1CoefficientMap]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_range #[``groupCohomology.mapShortComplex₁_exact]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingToKernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_range]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingKernelEquiv #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_range, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.invariantConnectingKernelEquiv #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingKernelEquiv, ``groupCohomology.H0Iso]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.invariantConnectingKernelEquiv, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientInvariantEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.pointClass_killed #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.preimage]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_killed #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.pointClass_killed]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_killed, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCosetH0_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.invariantConnectingKernelEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement_val #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCoset_connecting]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_order_eq_prime, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.invariantConnectingKernelEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_cyclic_card #[``Nat.card_zmultiples, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_coset #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.upperQuotient_card]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_prime_power_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_positive_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_prime_power_profile, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_prime_cyclic_coefficient_kernel #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_order_eq_prime, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_cyclic_card, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_positive_profile]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_all_invariant #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientInvariantEquiv #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH0Projection_zero #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_injective #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedH1CoefficientKernel #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnecting_range #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingToKernel #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedConnectingKernelEquiv #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.invariantConnectingKernelEquiv #[`T, `A] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `hp5, `hq, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_prime_power_profile #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCoset_order_eq_prime #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedCosetH0_order_eq_prime #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_cyclic_card #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_positive_profile #[`h, `hp5] #[`hclass, `hbad, `hcofixed, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_prime_cyclic_coefficient_kernel #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement]

end Note032FreyKernelDependencyAudit
