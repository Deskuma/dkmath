/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.IrregularNorm37
import DkMathTest.FLT.FreyTwo
import DkMathTest.NumberTheory.LegendreFreyJCentralSeat
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note007DependencyAudit"

/-!
# NOTE-007 実依存監査

全共役イデアル積のノルム、位相0の同じ根と単元、2進補正付き最小性、
真の j を要求する。非自明指標の分類や FLT 完成定理を外部供給しない。
-/
namespace Note007DependencyAudit
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
-- Traverse actual proof graphs, including opaque bodies and ideal/class-group maps.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.integerAut,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.intNorm_eq_prod,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.absNorm_map,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.map_relNorm_le_prod,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.eq_of_le_of_absNorm_eq,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.prod_map_eq_span_absNorm,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.classGroup_prod_eq_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_eq_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.zero_obstruction_eq_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.fixed_p_torsion_eq_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.fixed_p_primary_eq_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.characterComponent,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.trivial_characterComponent,
    ``DkMath.Lib.NumberTheory.FreyGapCubic.not_two_dvd_integral_c4,
    ``DkMath.FLT.Frey.Source.isMinimal_at_two,
    ``DkMath.FLT.Frey.Source.two_dvd_product,
    ``DkMath.FLT.Frey.Source.one_le_product_two_valuation,
    ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation_two,
    ``DkMath.FLT.Frey.Source.exponent_dvd_two_valuation_iff,
    ``DkMath.FLT.Frey.Source.good_or_multiplicative_at_two,
    ``DkMath.FLT.Frey.Source.hasMultiplicativeReduction_at_two,
    ``DkMath.FLT.Frey.Source.isMinimal_every_prime,
    ``DkMath.FLT.Frey.Source.good_or_multiplicative_every_prime,
    ``DkMath.FLT.Frey.Source.multiplicative_support_iff,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_obstruction_eq_one,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_root_principal,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_unit_generator,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_nonzero_trivial_iff,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_nontrivial_moves,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_eq,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reductionJ,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reductionJ_eq_zero,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.j_bridge_of_mem_support]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public NOTE-007 declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.GaloisIdealNorm.prod_map_eq_span_absNorm #[
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.intNorm_eq_prod,
    ``Algebra.norm_eq_prod_automorphisms,
    ``Ideal.relNorm_int, ``Ideal.absNorm_relNorm,
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.eq_of_le_of_absNorm_eq] true true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_eq_one #[
    ``DkMath.Lib.NumberTheory.GaloisIdealNorm.classGroup_prod_eq_one,
    ``ClassGroup.mk0_surjective,
    ``DkMath.Lib.NumberTheory.classGroup_map_mk0,
    ``IsCyclotomicExtension.Rat.galEquivZMod] true true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_unit_generator #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_orbit_norm,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_eq_one,
    ``DkMath.Lib.NumberTheory.IdealPowerObstruction.exists_unit_generator] false true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.fixed_p_primary_eq_one #[
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_eq_one,
    ``orderOf_dvd_of_pow_eq_one] true true
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.trivial_characterComponent #[
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.characterComponent,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.fixed_p_torsion_eq_one] true true
  checkRoot ``DkMath.FLT.Frey.Source.isMinimal_at_two #[
    ``DkMath.Lib.NumberTheory.FreyGapCubic.not_two_dvd_integral_c4,
    ``DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_c4] false true
  checkRoot ``DkMath.FLT.Frey.Source.hasMultiplicativeReduction_at_two #[
    ``WeierstrassCurve.HasMultiplicativeReduction,
    ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation_two,
    ``DkMath.FLT.Frey.Source.one_le_product_two_valuation] false true
  checkRoot ``DkMath.FLT.Frey.Source.good_or_multiplicative_every_prime #[
    ``DkMath.FLT.Frey.Source.good_or_multiplicative_at_two,
    ``DkMath.FLT.Frey.Source.good_or_multiplicative] false true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_eq #[
    ``WeierstrassCurve.j,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_isElliptic,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalCurve_discriminant] false true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.j_bridge_of_mem_support #[
    ``WeierstrassCurve.j,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reduction_isElliptic,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.reduction_c4_eq_zero,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.mem_primeSupport_iff] false true

end Note007DependencyAudit
