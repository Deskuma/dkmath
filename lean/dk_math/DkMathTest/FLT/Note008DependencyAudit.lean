/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.PrimeDepthTransport
import DkMathTest.Lib.FiniteSpectrumProjectors
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note008DependencyAudit"

/-!
# NOTE-008 公理と実依存の監査

実際の類群作用・有限補間・ノルムによる自明成分消去・記録済みState・
正規化曲線・有限Hensel桁を辿る。型だけでなく不透明な証明本体も調べる。
正則性providerやFLT終点を使って37の障害を消す迂回路を禁止する。
-/
namespace Note008DependencyAudit
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
-- Traverse ten proof graphs, up to 47,000 constants each, including opaque bodies and types.
run_cmd do
  let roots : Array Name := #[
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.linear_factor_mul_basis,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_eigen,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_apply_eigen,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.sum_projector,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.sum_projector_apply,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_idempotent,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_orthogonal,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.decompose,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.directSumEquiv,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.exists_nonzero_projector,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.torsionGroup,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.Space,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_injective,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_zero,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_torsion,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.spaceModule,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_smul,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.actionMul,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.linearAction,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_action,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.action,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.generator,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.exists_generator_pow,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.exponent,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character_generator,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character_injective,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.operator,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.operator_pow,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.nodal_eq,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.aeval_nodal,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.component,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_idempotent,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_orthogonal,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.mem_component_iff,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.decomposition,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.sum_projector,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.character_one,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.component_one,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_one,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.exists_nontrivial_component,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_obstruction_dichotomy,
    ``DkMath.FLT.Kummer.IrregularPrime37.observeVector,
    ``DkMath.FLT.Kummer.IrregularPrime37.underlying_observeVector,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_nontrivial_character,
    ``DkMath.FLT.Frey.Source.two_discriminant_cast,
    ``DkMath.FLT.Frey.Source.discriminant_cast_profile,
    ``DkMath.FLT.Frey.Source.prime_not_dvd_eight,
    ``DkMath.FLT.Frey.Source.not_exponent_dvd_two_valuation,
    ``DkMath.FLT.Frey.Source.exponent_dvd_valuation_iff_ne_two,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_valuation,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_exact_depth,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_depth_of_mem_support,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralPolynomial,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralPolynomial_eval,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.centralPolynomial_derivative_not_dvd,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.existsUnique_central_next_digit,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_depth_of_exact_divisibility,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.exists_central_exact_jDepth,
    ``DkMath.FLT.Frey.Source.centralSeat_depth_pair,
    ``DkMath.FLT.Frey.Source.oldSupport_depth_pair]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {roots.size} public NOTE-008 declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.directSumEquiv #[
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_eigen,
    ``Lagrange.sum_basis,
    ``DirectSum.linearEquivFunOnFintype] true true
  checkRoot ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.decomposition #[
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.operator_pow,
    ``ClassGroup.mulEquiv,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.sigma,
    ``DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.directSumEquiv] true true
  checkRoot ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.mem_component_iff #[
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.characterComponent,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_smul,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.underlying_action] true true
  checkRoot ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_one #[
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_eq_one,
    ``DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.trivial_characterComponent] true true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_obstruction_dichotomy #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_zero_obstruction_eq_one,
    ``DkMath.FLT.Kummer.IrregularPrime37.observe_nonzero_trivial_iff] false true
  checkRoot ``DkMath.FLT.Kummer.IrregularPrime37.observe_nontrivial_character #[
    ``DkMath.FLT.Kummer.IrregularPrime37.observeVector,
    ``DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.exists_nontrivial_component] false true
  checkRoot ``DkMath.FLT.Frey.Source.exponent_dvd_valuation_iff_ne_two #[
    ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation_two,
    ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation,
    ``DkMath.FLT.Frey.Source.prime_not_dvd_eight] false true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_valuation #[
    ``WeierstrassCurve.j,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.prime_not_dvd_coordinates,
    ``padicValRat.div] false true
  checkRoot ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.exists_central_exact_jDepth #[
    ``DkMath.Lib.NumberTheory.exists_polynomial_exact_depth_digit,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_depth_of_exact_divisibility] false true
  checkRoot ``DkMath.FLT.Frey.Source.oldSupport_depth_pair #[
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.mem_primeSupport_iff,
    ``DkMath.FLT.Frey.Source.minimal_discriminant_valuation,
    ``DkMath.NumberTheory.Legendre.FreyC4CentralSeat.rationalJ_valuation] false true

#print axioms DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.decomposition
#print axioms DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition.projector_one
#print axioms DkMath.FLT.Kummer.IrregularPrime37.observe_nontrivial_character
#print axioms DkMath.FLT.Frey.Source.exponent_dvd_valuation_iff_ne_two
#print axioms DkMath.NumberTheory.Legendre.FreyC4CentralSeat.exists_central_exact_jDepth

end Note008DependencyAudit
