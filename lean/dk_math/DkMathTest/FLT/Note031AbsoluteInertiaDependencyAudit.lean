/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.AbsoluteInertiaLocalGlobal
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031AbsoluteInertiaDependencyAudit"

/-!
# NOTE-031-001B: 持ち上げ・開部分群・同じFrey表現への輸送を監査する

全新規公開宣言の公理と、主要な経路の型・opaque本体を検査する。
profinite剰余体作用の全射性、局所化DVR、付値環の分数表示、Minkowskiの有限算術、
Krull開性、実際のtorsion有限性と開核へ到達することを要求する。
Frey入口にも局所条件は残すが、生成性・持ち上げ・開核の外部providerを追加しない。
旧FLT終点・外部provider・Kummer・折り返し整数核への依存は禁止する。
-/
namespace Note031AbsoluteInertiaDependencyAudit
open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx ||
    s.startsWith "DkMath.Lib.NumberTheory.RegularKummer." ||
    s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit." || s.startsWith "FltRegular." || s.startsWith "P2M." ||
    s.startsWith "P2MW." || s.startsWith "FreyPackage." ||
    s.contains "fermatLastTheorem" || s.contains "fermat_last_theorem" ||
    s.contains "fermatThree_no_positive_solution" ||
    (`DkMath.FLT.Kummer).isPrefixOf (privateToUserName n)

private def checkRoot (root : Name) (required : Array Name) (neutral : Bool := false)
    (algebraOnly : Bool := false) (withoutFolded : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let s := (privateToUserName n).toString
    if forbidden n || (neutral && s.startsWith "DkMath.FLT.") ||
        (withoutFolded && s.startsWith "DkMath.Lib.NumberTheory.FoldedValuationOrbit.") ||
        (algebraOnly && (s.startsWith "NumberField." || s.startsWith "Ideal.inertia" ||
          s.startsWith "Ideal.ramification" ||
          s.startsWith "DkMath.Lib.NumberTheory." ||
          s.startsWith "WeierstrassCurve.")) then
      throwError "Forbidden dependency: {n}"
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

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input missing in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; explicit arithmetic guards and remaining inputs retained."

set_option maxHeartbeats 0 in
-- 型・opaque本体を含む有限の依存グラフを走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.ValuationInertia.LiesOverPrime,
    ``DkMath.Lib.NumberTheory.ValuationInertia.inertiaSubgroupIn,
    ``DkMath.Lib.NumberTheory.IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure,
    ``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_div_rep_or_inv_div_rep_of_ne_bot,
    ``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction,
    ``DkMath.Lib.NumberTheory.ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.fixedSubgroup_isOpen,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.cofixedSubgroup_isOpen,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isFixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isCofixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.fixed_or_cofixed_of_inertia_common_side,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isFixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isCofixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fixed_or_cofixed_of_inertia_common_side,
    ``DkMath.FLT.Frey.Source.residual_isFixedOn_of_inertia,
    ``DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia,
    ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_of_inertia_common_side]
  let regression : Array Name := #[``AbsoluteInertiaLocalGlobalTest.lift_preserves_nontriviality,
    ``AbsoluteInertiaLocalGlobalTest.proper_open_subgroup_has_local_witness,
    ``AbsoluteInertiaLocalGlobalTest.not_liesOver_one,
    ``AbsoluteInertiaLocalGlobalTest.integral_fraction_denominator_ne_zero,
    ``AbsoluteInertiaLocalGlobalTest.source37_fixed,
    ``AbsoluteInertiaLocalGlobalTest.source37_cofixed,
    ``AbsoluteInertiaLocalGlobalTest.source37_common_side,
    ``AbsoluteInertiaLocalGlobalTest.source37_cofixed_failure_local_witness,
    ``AbsoluteInertiaLocalGlobalTest.inconsistent_side_boundary]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure #[``Ideal.Quotient.stabilizerHom_surjective_of_profinite,
    ``Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_div_rep_or_inv_div_rep_of_ne_bot #[``ValuationRing.cond,
    ``IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction #[``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_div_rep_or_inv_div_rep_of_ne_bot] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence #[``DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction,
    ``Ideal.image_subset_nonunits_valuationSubring,
    ``DkMath.Lib.NumberTheory.ValuationInertia.inertiaSubgroupIn] true false
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia #[``DkMath.Lib.NumberTheory.IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure,
    ``DkMath.Lib.NumberTheory.ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence] true false
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia,
    ``DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``krullTopology_mem_nhds_one_iff_of_normal,
    ``NumberField.abs_discr_gt_two] true false
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isFixedOn_of_inertia #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.fixedSubgroup_isOpen] true false
  checkRoot ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isCofixedOn_of_inertia #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
    ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.cofixedSubgroup_isOpen] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isFixedOn_of_inertia #[``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isFixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finite_torsion_of_ne_zero,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_stabilizer_isOpen] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isCofixedOn_of_inertia #[``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isCofixedOn_of_inertia,
    ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.representationKernel_isOpen_of_ne_zero] true false
  checkRoot ``DkMath.FLT.Frey.Source.residual_isFixedOn_of_inertia #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isFixedOn_of_inertia,
    ``DkMath.FLT.Frey.Source.rationalCurve] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia #[``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isCofixedOn_of_inertia,
    ``DkMath.FLT.Frey.Source.rationalCurve] false false
  checkRoot ``AbsoluteInertiaLocalGlobalTest.lift_preserves_nontriviality #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia] true false
  checkRoot ``AbsoluteInertiaLocalGlobalTest.proper_open_subgroup_has_local_witness #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le] true false
  checkRoot ``AbsoluteInertiaLocalGlobalTest.source37_cofixed_failure_local_witness #[``DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia] false false
  checkRoot ``AbsoluteInertiaLocalGlobalTest.inconsistent_side_boundary #[``InertiaLocalGlobalTest.SideBoundary.line_finrank,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_fixed,
    ``InertiaLocalGlobalTest.SideBoundary.not_global_cofixed] true true
  checkInputs ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le #[`H, `hopen, `hunr] #[`hgen, `hlift, `hglobal]
  checkInputs ``DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation.isCofixedOn_of_inertia #[`ρ, `N, `hopen, `hlocal] #[`hgen, `hlift, `hglobal]
  checkInputs ``DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia #[`S, `N, `hlocal] #[`hgen, `hlift, `hopen, `hrat, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_of_inertia_common_side #[`S, `N, `hside] #[`hgen, `hlift, `hopen, `hrat, `hcases, `hno]

#print axioms DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le
#print axioms DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia
#print axioms AbsoluteInertiaLocalGlobalTest.proper_open_subgroup_has_local_witness

end Note031AbsoluteInertiaDependencyAudit
