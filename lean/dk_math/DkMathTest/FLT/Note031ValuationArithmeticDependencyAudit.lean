/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyValuationArithmetic
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031ValuationArithmeticDependencyAudit"

/-!
# NOTE-031-002A: 算術・実際のtorsion座標の整性・合同の境界の監査

全公開宣言の公理と主要経路の型・opaque本体を走査する。
整数の付値、最高次項の支配、実際の除法多項式の根、モニック二次式、
慣性の剰余体作用の核へ到達することを要求する。
旧FLT終点・外部provider・Kummer・固定点消滅の整数核を使わない。
合同と固定を混同せず、指数の単元性・p≠q・非零整数条件を公開入力に保持する。
-/
namespace Note031ValuationArithmeticDependencyAudit
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
-- 型とopaque本体を含む有限の依存グラフを走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.Algebra.ValuationPolynomial.valuation_eval_of_pole,
    ``DkMath.Lib.Algebra.ValuationPolynomial.valuation_root_le_one,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.charP_residueField,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_pow_padicValInt,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_pow_of_dvd,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_x_mem,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.y_mem_of_x_mem,
    ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem,
    ``DkMath.FLT.Frey.Source.valuationModel,
    ``DkMath.FLT.Frey.Source.valuationModel_map,
    ``DkMath.FLT.Frey.Source.curve_discriminant_ne_zero,
    ``DkMath.FLT.Frey.Source.valuation_discriminant_eq,
    ``DkMath.FLT.Frey.Source.valuation_discriminant_pth_power,
    ``DkMath.FLT.Frey.Source.valuation_c4_eq_one,
    ``DkMath.FLT.Frey.Source.valuation_reduction_isElliptic,
    ``DkMath.FLT.Frey.Source.residual_coordinates_mem,
    ``DkMath.FLT.Frey.Source.residual_inertia_coordinate_congruence]
  let regression : Array Name := #[``FreyValuationArithmeticTest.curveInt,
    ``FreyValuationArithmeticTest.curve,
    ``FreyValuationArithmeticTest.curve_isElliptic,
    ``FreyValuationArithmeticTest.point_nonsingular,
    ``FreyValuationArithmeticTest.point,
    ``FreyValuationArithmeticTest.point_nonzero_two_torsion,
    ``FreyValuationArithmeticTest.point_integral_at_three,
    ``FreyValuationArithmeticTest.point_not_integral_at_two,
    ``FreyValuationArithmeticTest.unit_hypothesis_boundary,
    ``FreyValuationArithmeticTest.congruence_does_not_imply_equality,
    ``FreyValuationArithmeticTest.zero_default_boundary,
    ``FreyValuationArithmeticTest.source37_discriminant,
    ``FreyValuationArithmeticTest.source37_at_p_arithmetic,
    ``FreyValuationArithmeticTest.source37_good_reduction,
    ``FreyValuationArithmeticTest.source37_bad_c4,
    ``FreyValuationArithmeticTest.source37_coordinates,
    ``FreyValuationArithmeticTest.source37_inertia_congruence]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.Algebra.ValuationPolynomial.valuation_root_le_one #[``DkMath.Lib.Algebra.ValuationPolynomial.valuation_eval_of_pole,
    ``Valuation.map_sum_lt] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_pow_padicValInt #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd,
    ``pow_succ_padicValNat_not_dvd] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.charP_residueField #[``CharP.charP_iff_prime_eq_zero] true false
  checkRoot ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits #[``DkMath.Lib.NumberTheory.ValuationInertia.inertiaSubgroupIn,
    ``ValuationSubring.inertiaSubgroup] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_x_mem #[``DkMath.Lib.Algebra.ValuationPolynomial.valuation_root_le_one,
    ``DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ,
    ``WeierstrassCurve.leadingCoeff_ΨSq] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.y_mem_of_x_mem #[``IsIntegrallyClosed.isIntegral_iff] true false
  checkRoot ``DkMath.FLT.Frey.Source.valuation_discriminant_eq #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_pow_padicValInt,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.integral_valuation_of_solution,
    ``DkMath.FLT.Frey.Source.curve_discriminant_ne_zero] false false
  checkRoot ``DkMath.FLT.Frey.Source.valuation_reduction_isElliptic #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd,
    ``DkMath.Lib.NumberTheory.FreyPrimeValuation.prime_dvd_integral_discriminant_iff] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_coordinates_mem #[``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem,
    ``DkMath.FLT.Frey.Source.valuationModel_map] false false
  checkRoot ``DkMath.FLT.Frey.Source.residual_inertia_coordinate_congruence #[``DkMath.FLT.Frey.Source.residual_coordinates_mem,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits] false false
  checkRoot ``FreyValuationArithmeticTest.point_integral_at_three #[``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem,
    ``FreyValuationArithmeticTest.point_nonzero_two_torsion] true false
  checkRoot ``FreyValuationArithmeticTest.unit_hypothesis_boundary #[``FreyValuationArithmeticTest.curve_isElliptic,
    ``FreyValuationArithmeticTest.point_nonzero_two_torsion,
    ``FreyValuationArithmeticTest.point_not_integral_at_two] true false
  checkRoot ``FreyValuationArithmeticTest.congruence_does_not_imply_equality #[] true false
  checkRoot ``FreyValuationArithmeticTest.zero_default_boundary #[] true false
  checkInputs ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_pow_padicValInt #[`hq, `hA, `hz] #[`hfix, `hcases]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem #[`W, `E, `hmodel, `hn, `h, `hkill] #[`hgood, `hfix, `hcases]
  checkInputs ``DkMath.FLT.Frey.Source.residual_coordinates_mem #[`S, `hq, `hqp, `hA, `h, `hkill] #[`hgood, `hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_inertia_coordinate_congruence #[`S, `hq, `hqp, `hA, `σ, `hσ, `hkill] #[`hfix, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.valuation_discriminant_eq #[`S, `hq2, `hA] #[`hqp, `hfix, `hcases]

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem
#print axioms DkMath.FLT.Frey.Source.residual_inertia_coordinate_congruence
#print axioms FreyValuationArithmeticTest.unit_hypothesis_boundary

end Note031ValuationArithmeticDependencyAudit
