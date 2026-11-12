/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyArithmetic
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.FreyArithmeticDependencyAudit"

/-! NOTE-005: actual curve invariants, variable changes and valuation proofs must occur in
these proof graphs. No completed FLT, Kummer regularity or modularity theorem may replace them. -/

namespace FreyArithmeticDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
    s.toLower.contains "herbrand" || s.toLower.contains "ribet" ||
    s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
    s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution"

private def globalProvider (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  s.startsWith "DkMath.FLT.Kummer." || s.startsWith "FreyPackage." ||
    s.contains "classGroupPTorsionFreeAt" || s.contains "KummerUnitPowerCriterion"

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false) (localOnly : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n || (localOnly && globalProvider (privateToUserName n)) ||
        (neutral && (privateToUserName n).toString.startsWith "DkMath.FLT.") then throwError "Forbidden dependency: {n}"
    let some info := env.checked.get.find? n | throwError "Missing constant: {n}"
    pending := pending ++ info.type.getUsedConstants
    if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    match info.value? (allowOpaque := true) with
    | some value => pending := pending ++ value.getUsedConstants
    | none =>
      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => throwError "Unreadable body: {n}"
      | _ => pure ()
  for n in required do
    unless visited.contains n do throwError "Required provider absent: {n}"
  logInfo m!"PASS: {root}; {visited.size} reachable constants; expected providers present."

set_option maxHeartbeats 0 in
-- Audit complete transitive proof graphs, including opaque bodies and model definitions.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.FreyGapCubic.cubic,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.cubic_factorization,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.root_gap_product,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.cubic_discriminant,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.naive,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.naive_discriminant,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.naive_c4,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalizeChange,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized_eq_change,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized_discriminant,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized_c4,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized_isElliptic,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.IntegralNormalization,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.integral,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.integral_map,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.integral_c4,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.integral_discriminant,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.gnFactor,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.sum_eq_gap_gn,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.naive_discriminant_gn,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.normalized_discriminant_gn,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.gap_product_of_solution,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.normalized_discriminant_of_solution,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.normalized_c4_of_solution,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.normalization_of_oriented,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.integral_discriminant_gn,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.integral_discriminant_of_solution,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_not_dvd_c4_form,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.not_dvd_integral_c4,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.valuation_scaled_power,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.valuation_two_eq_zero,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.valuation_of_solution,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.valuation_of_solution_odd,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.integral_valuation_of_solution,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.exponent_dvd_integral_valuation,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_dvd_integral_discriminant_iff,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.valuation_gn,
    ``DkMath.FLT.Frey.Source,
    ``DkMath.FLT.Frey.Source.product_ne_zero,
    ``DkMath.FLT.Frey.Source.curve,
    ``DkMath.FLT.Frey.Source.rationalCurve,
    ``DkMath.FLT.Frey.Source.curve_map,
    ``DkMath.FLT.Frey.Source.rationalCurve_isElliptic,
    ``DkMath.FLT.Frey.Source.discriminant_gn,
    ``DkMath.FLT.Frey.Source.local_arithmetic,
    ``DkMath.FLT.Frey.Source.reduction_isElliptic,
    ``DkMath.FLT.Frey.ofOriented]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public NOTE-005 declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized_discriminant #[
    ``WeierstrassCurve.variableChange_Δ,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalizeChange,
    ``WeierstrassCurve.Δ] true true
  checkRoot ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.integral_discriminant_gn #[
    ``DkMath.Lib.NumberTheory.FreyGapCubic.integral_map,
    ``DkMath.Lib.Cosmic.odd_sum_eq_mul_gtail_one,
    ``WeierstrassCurve.map_Δ] true true
  checkRoot ``DkMath.Lib.NumberTheory.FreyPrimeValuation.integral_valuation_of_solution #[
    ``padicValRat.div, ``padicValRat.pow,
    ``DkMath.Lib.NumberTheory.GNFreyDiscriminant.normalized_discriminant_of_solution] true true
  checkRoot ``DkMath.FLT.Frey.Source.local_arithmetic #[
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_not_dvd_c4_form,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_dvd_integral_discriminant_iff,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.integral_valuation_of_solution] false true
  checkRoot ``DkMath.FLT.Frey.Source.reduction_isElliptic #[
    ``WeierstrassCurve.map_Δ,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_dvd_integral_discriminant_iff] false true

end FreyArithmeticDependencyAudit
