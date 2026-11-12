/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.GaloisPhaseOrbitNorm
import DkMathTest.FLT.FreyLocalReduction
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.SectionFourDependencyAudit"

/-!
# NOTE-006 §4 / IRR-007 の実依存監査

公開宣言の公理と、主要証明の型・opaque 本体の推移閉包を検査する。
実際の円分体の作用・全位相積、実際の局所化・座標変換・最小性を要求する。
-/

namespace SectionFourDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
    s.toLower.contains "herbrand" || s.toLower.contains "ribet" ||
    s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
    s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution"

private def globalProvider (n : Name) : Bool :=
  (#[`DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt,
    `DkMath.Lib.NumberTheory.KummerUnitPowerCriterion,
    `DkMath.FLT.Kummer.RegularDescent.Conditions,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_quotient_roots,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_descent_roots,
    `DkMath.FLT.Kummer.RegularDescent.State.exists_weighted_successor,
    `DkMath.FLT.Kummer.RegularDescent.descent_step,
    `DkMath.FLT.Kummer.RegularDescent.no_state,
    `DkMath.FLT.Kummer.RegularDescent.ratio_power,
    `DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    `DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt]).any (fun root => root.isPrefixOf n)

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
-- Complete proof graphs include the real class-group equivalences and DVR models.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.nonzeroPhaseEquiv,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.nonzeroPhaseEquiv_apply,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.exists_phaseMul_one,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.prod_eq_zero_mul_orbit,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.zero_mul_orbit_norm,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_mul,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_fixed,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_torsion,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.zero_mul_orbitNorm,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_c4,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.hasMultiplicativeReduction_of_c4,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_discriminant,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.hasGoodReduction_of_isUnit_discriminant,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.primeIdeal,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.primeIdeal_isPrime,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.LocalRing,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.localRing_dvr,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.localRatAlgebra,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.localRatTower,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.localRatFractionRing,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isUnit_local_iff,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.mem_maximal_local_iff,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_at_prime_of_not_dvd_c4,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.hasMultiplicativeReduction_at_prime,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.hasGoodReduction_at_prime,
    ``DkMath.FLT.Frey.Source.hasMultiplicativeReduction,
    ``DkMath.FLT.Frey.Source.hasGoodReduction,
    ``DkMath.FLT.Frey.Source.isMinimal_at_odd_prime,
    ``DkMath.FLT.Frey.Source.good_or_multiplicative,
    ``DkMath.FLT.Frey.Source.hasMultiplicativeReduction_iff,
    ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation,
    ``DkMath.FLT.Frey.Source.minimal_discriminant_exponent_dvd,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_fixed,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_orbit_norm]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public section-4 declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.zero_mul_orbit_norm #[
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.nonzeroPhaseEquiv,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.prod_eq_zero_mul_orbit] true true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.zero_mul_orbitNorm #[
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.obstruction_int,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.exists_ramifier_unit,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.phase_root_galois] true true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_orbit_norm #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_galois,
    ``DkMath.FLT.Kummer.IrregularPrime37.product_obstruction_one,
    ``DkMath.Lib.NumberTheory.RamifiedPhasePacket.zero_mul_orbit_norm,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.root_transport_of_unit] false true
  checkRoot ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_c4 #[
    ``WeierstrassCurve.IsMinimal,
    ``WeierstrassCurve.variableChange_c₄,
    ``WeierstrassCurve.variableChange_Δ,
    ``WeierstrassCurve.valuation_Δ_aux] true true
  checkRoot ``DkMath.FLT.Frey.Source.hasMultiplicativeReduction #[
    ``WeierstrassCurve.HasMultiplicativeReduction,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.LocalRing,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_c4,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.not_dvd_integral_c4,
    ``DkMath.FLT.Frey.Source.curve_map] false true
  checkRoot ``DkMath.FLT.Frey.Source.hasGoodReduction #[
    ``WeierstrassCurve.HasGoodReduction,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_discriminant,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_dvd_integral_discriminant_iff] false true
  checkRoot ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation #[
    ``DkMath.FLT.Frey.Source.isMinimal_at_odd_prime,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.valuation_of_solution_odd] false true

end SectionFourDependencyAudit
