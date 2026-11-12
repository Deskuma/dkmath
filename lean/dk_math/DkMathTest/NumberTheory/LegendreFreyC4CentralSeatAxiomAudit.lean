/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreFreyC4CentralSeat
import Lean.Util.FoldConsts

#print "file: DkMathTest.NumberTheory.LegendreFreyC4CentralSeatAxiomAudit"

/-! NOTE-006 §3: check the actual Frey invariants, reduction map and finite-field order
proof. No Legendre conjecture/full-cover hypothesis or completed FLT may enter these graphs. -/

namespace LegendreFreyC4CentralSeatAxiomAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
    s.toLower.contains "herbrand" || s.toLower.contains "ribet" ||
    s.contains "LegendreConjecture" || s.contains "SquareOffsetsFullyCovered" ||
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
-- Traverse complete model/finite-field proof graphs, including opaque bodies.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat_eq_square_add,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat_offset,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat_mem_squareCell,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat_coprime_gaps,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat_odd,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.divisor_ne_two,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_not_dvd_coordinates,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.mem_primeSupport_iff,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_bridge_of_mem_support,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.curve,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_eq_change,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_isElliptic,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.curve_c4,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_c4,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.curve_discriminant,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_discriminant,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.integralNormalization_iff,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.integral_c4,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_not_dvd_discriminant,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_dvd_c4,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reduction_isElliptic,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reduction_c4_eq_zero,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.orderOf_eq_three,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_mod_three,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_three_or_mod_three,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_modEq_one,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_bridge]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public NOTE-006 central-seat declarations; standard logical axioms only."
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_c4 #[
    ``DkMath.Lib.NumberTheory.FreyGapCubic.normalized_c4,
    ``WeierstrassCurve.variableChange_c₄] true true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_not_dvd_discriminant #[
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralSeat_coprime_gaps,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.naive_discriminant,
    ``WeierstrassCurve.Δ] true true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reduction_isElliptic #[
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_not_dvd_discriminant,
    ``WeierstrassCurve.map_Δ] true true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_mod_three #[
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.orderOf_eq_three,
    ``ZMod.orderOf_dvd_card_sub_one] true true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_bridge #[
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_dvd_c4,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_not_dvd_discriminant,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_three_or_mod_three] true true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_bridge_of_mem_support #[
    ``DkMath.NumberTheory.Legendre.mem_squareOffsetPrimeSupport,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_bridge] true true

end LegendreFreyC4CentralSeatAxiomAudit
