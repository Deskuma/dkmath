/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.Kummer.ElevenThirteenRegularTransport
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Kummer.ElevenThirteenDependencyAudit"

/-! Audit every new public declaration, then traverse actual proof graphs including
opaque bodies and constructors. Reject completed FLT endpoints and old sevenfold
base/step proofs, in addition to unexpected axioms. -/

namespace ElevenThirteenDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx || s.startsWith "FltRegular." || s.startsWith "P2MW." ||
  s.contains "fermatLastTheorem" || s.contains "fermatThree_no_positive_solution" ||
  s.contains "fermatFive_no_positive_solution" || s.contains "fermatSeven_no_positive_solution" ||
  s == "DkMath.FLT.Kummer.SevenDescent.descent_step" ||
  s == "DkMath.FLT.Kummer.SevenDescent.no_state_one"

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
-- Audit the shared Hilbert/Kummer arithmetic and both concrete State proof graphs.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.NumberTheory.RegularKummer.exists_zeta_sub_one_dvd_sub_Int,
    ``DkMath.Lib.NumberTheory.RegularKummer.exists_dvd_pow_sub_Int_pow,
    ``DkMath.Lib.NumberTheory.RegularKummer.quotient_zero_sub_one_comp_aut,
    ``DkMath.Lib.NumberTheory.RegularKummer.zeta_sub_one_dvd_trace_sub_smul,
    ``DkMath.Lib.NumberTheory.RegularKummer.zeta_sub_one_pow_dvd_norm_sub_pow,
    ``DkMath.Lib.NumberTheory.RegularKummer.norm_add_one_smul_of_isUnit,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers,
    ``DkMath.Lib.NumberTheory.RegularKummer.cyclotomic_minpoly_of_primitiveRoot,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.equiv,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.zeta,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.equiv_zeta,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.prime_one_sub_zeta,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.not_isUnit_one_sub_zeta,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.one_sub_zeta_dvd_int_iff,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.one_sub_zeta_dvd,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.isCoprime_one_sub_zeta,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.exists_dvd_int,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.powerBasis,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.powerBasis_dim,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.nontrivial,
    ``DkMath.Lib.NumberTheory.RegularKummer.CyclotomicIntegers.charZero,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.IsMaximal,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.isMaximal,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.index,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.IsFundamental,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.IsFundamental.maximal',
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.IsFundamental.existence,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.IsFundamental.lemma2,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.IsFundamental.corollary,
    ``DkMath.Lib.NumberTheory.RegularKummer.RelativeUnits,
    ``DkMath.Lib.NumberTheory.RegularKummer.norm_eq_prod_pow_gen,
    ``DkMath.Lib.NumberTheory.RegularKummer.Hilbert92_aux0,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsMap,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsMap_mk,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsMap_one,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsMap_mul_apply,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsMapHom,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsMapHom_apply,
    ``DkMath.Lib.NumberTheory.RegularKummer.isTors',
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsWithGenerator,
    ``DkMath.Lib.NumberTheory.RegularKummer.unitToU,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_one,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_mul,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_inv,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_div,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_prod,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_pow,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_zpow,
    ``DkMath.Lib.NumberTheory.RegularKummer.unit_to_U_map,
    ``DkMath.Lib.NumberTheory.RegularKummer.exists_pow_smul_eq_and_not_dvd,
    ``DkMath.Lib.NumberTheory.RegularKummer.lh_pow_free_aux,
    ``DkMath.Lib.NumberTheory.RegularKummer.lh_pow_free',
    ``DkMath.Lib.NumberTheory.RegularKummer.lh_pow_free,
    ``DkMath.Lib.NumberTheory.RegularKummer.Hilbert92_aux1,
    ``DkMath.Lib.NumberTheory.RegularKummer.relativeUnitsModule_zeta_smul,
    ``DkMath.Lib.NumberTheory.RegularKummer.unitlifts,
    ``DkMath.Lib.NumberTheory.RegularKummer.unitlifts_spec,
    ``DkMath.Lib.NumberTheory.RegularKummer.u_lemma2,
    ``DkMath.Lib.NumberTheory.RegularKummer.Hilbert92_aux2,
    ``DkMath.Lib.NumberTheory.RegularKummer.relative_units_rank_of_isUnramified,
    ``DkMath.Lib.NumberTheory.RegularKummer.finrank_G,
    ``DkMath.Lib.NumberTheory.RegularKummer.Hilbert91,
    ``DkMath.Lib.NumberTheory.RegularKummer.h_exists',
    ``DkMath.Lib.NumberTheory.RegularKummer.almostHilbert92,
    ``DkMath.Lib.NumberTheory.RegularKummer.Hilbert92,
    ``DkMath.Lib.NumberTheory.RegularKummer.comap_span_galRestrict_eq_of_cyclic,
    ``DkMath.Lib.NumberTheory.RegularKummer.exists_not_isPrincipal_and_isPrincipal_map_aux,
    ``DkMath.Lib.NumberTheory.RegularKummer.ideal_power_isPrincipal_of_isPrincipal_map,
    ``DkMath.Lib.NumberTheory.RegularKummer.exists_not_isPrincipal_and_isPrincipal_map,
    ``DkMath.Lib.NumberTheory.RegularKummer.dvd_card_classGroup_of_unramified_isCyclic,
    ``DkMath.Lib.NumberTheory.RegularKummer.zeta_sub_one_pow_dvd_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.natDegree_poly_aux,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.monic_poly_aux,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.poly_spec,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.monic_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.natDegree_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.map_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.irreducible_map_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.aeval_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.polyRoot,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.roots_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.splits_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.map_poly_eq_prod,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.minpoly_polyRoot'',
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.minpoly_polyRoot',
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.separable_poly_aux,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.separable_poly,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.polyRoot_spec,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.mem_adjoin_polyRoot,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.isUnramified,
    ``DkMath.Lib.NumberTheory.RegularKummer.exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one,
    ``DkMath.Lib.NumberTheory.RegularKummer.eq_pow_prime_of_unit_of_congruent,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.existence0,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.finrank_spanA,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.ex_not_mem,
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.existence',
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.existence'',
    ``DkMath.Lib.NumberTheory.RegularKummer.systemOfUnits.existence,
    ``DkMath.Lib.NumberTheory.RegularKummer.algebraMap_injective_of_isIntegralClosure,
    ``DkMath.Lib.NumberTheory.RegularKummer.comap_map_eq_of_unramified,
    ``DkMath.Lib.NumberTheory.RegularKummer.isUnramifiedAt_of_Separable_minpoly',
    ``DkMath.Lib.NumberTheory.RegularKummer.isUnramifiedAt_of_Separable_minpoly,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.Proof.minkowski_bound_floor,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.Proof.minkowski_bound,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.Proof.not_pow_orderOf_le,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.Proof.isPrincipal_of_liesOver_twentythree,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.Proof.eleven_pid,
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.eleven_pid,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.g3,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.g3_natDegree,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.g3_irreducible,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.F27,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.F27_root,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.F27_three,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.CubicResidue.isPrincipal_of_liesOver_three,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.isPrincipal_of_mem_primesOver_three,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.exists_primesOver_three_isPrincipal,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.span_mem_primesOver_of_cert,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.exists_primesOver_lt,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.minkowski_bound_lt,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.minkowski_bound,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.dispatchA,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.dispatchB,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.dispatchC,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.dispatchD,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.MinkowskiThirteen.thirteen_pid,
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.thirteen_pid,
    ``DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.kummer_unit_power_criterion_of_ringEquiv,
    ``DkMath.FLT.Kummer.RegularDescent.eleven_classGroup_card_eq_one,
    ``DkMath.FLT.Kummer.RegularDescent.eleven_classGroup_torsion_free,
    ``DkMath.FLT.Kummer.RegularDescent.eleven_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.RegularDescent.eleven_conditions,
    ``DkMath.FLT.Kummer.RegularDescent.no_eleven_state,
    ``DkMath.FLT.Kummer.RegularDescent.thirteen_classGroup_card_eq_one,
    ``DkMath.FLT.Kummer.RegularDescent.thirteen_classGroup_torsion_free,
    ``DkMath.FLT.Kummer.RegularDescent.thirteen_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.RegularDescent.thirteen_conditions,
    ``DkMath.FLT.Kummer.RegularDescent.no_thirteen_state]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} new explicit declarations; standard logical axioms only."
  checkRoot ``DkMath.FLT.Kummer.regular_kummer_unit_power_criterion #[
    ``DkMath.Lib.NumberTheory.RegularKummer.eq_pow_prime_of_unit_of_congruent,
    ``DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.isUnramified,
    ``DkMath.Lib.NumberTheory.RegularKummer.dvd_card_classGroup_of_unramified_isCyclic,
    ``DkMath.Lib.NumberTheory.RegularKummer.Hilbert92]
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.no_eleven_state #[
    ``DkMath.Lib.NumberTheory.CyclotomicElevenPID.eleven_pid,
    ``DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.RegularDescent.eleven_classGroup_torsion_free,
    ``DkMath.FLT.Kummer.RegularDescent.no_state,
    ``DkMath.FLT.Kummer.RegularDescent.descent_step]
  checkRoot ``DkMath.FLT.Kummer.RegularDescent.no_thirteen_state #[
    ``DkMath.Lib.NumberTheory.CyclotomicThirteenPID.thirteen_pid,
    ``DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    ``DkMath.FLT.Kummer.RegularDescent.thirteen_classGroup_torsion_free,
    ``DkMath.FLT.Kummer.RegularDescent.no_state,
    ``DkMath.FLT.Kummer.RegularDescent.descent_step]

end ElevenThirteenDependencyAudit
