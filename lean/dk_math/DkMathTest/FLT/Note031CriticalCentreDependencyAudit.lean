/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.FLT.FreyCriticalCentre
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Note031CriticalCentreDependencyAudit"

/-!
# NOTE-031-002C2: 臨界中心の存在・深さ・慣性固定の依存を監査する

方程式の積差恒等式、実際の付値環での候補選択と整性、剰余特異点への接続、
奇素数での平方根の符号分離を確認する。中心や固定のprovider、旧FLT終点を使わない。
型とopaque本体を走査し、構造体のコンストラクタの依存も確認する。
-/
namespace Note031CriticalCentreDependencyAudit
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
        (algebraOnly && (s.startsWith "Valuation." || s.startsWith "ValuationSubring." ||
          s.startsWith "DkMath.Lib.NumberTheory.Valuation" ||
          s.startsWith "DkMath.Lib.NumberTheory.EllipticCriticalCentre." ||
          s.startsWith "NumberField." || s.startsWith "Ideal.inertia")) then
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
-- 型とopaque本体を含む有限グラフを全走査するための上限解除。
run_cmd do
  let production : Array Name := #[``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.equationDefect,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.completedCubic,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.criticalQuadratic,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.complete_square,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.completedCubic_critical_relation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.derivative_relation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.node_square_sub_c4,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.centreX,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.centreY,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.centreX_relation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.node_at_centreX,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.derivativeY_at_centre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.criticalQuadratic_at_centre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.derivativeX_at_centre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_at_centre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.centreY_square,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.c4_mul_centreX,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_mul_opposite,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_sub_opposite,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.map_equationDefect,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.translated_defect,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.translated_defect_factor,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.exists_criticalCentre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.node_square,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.translated_equation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.residue_singular,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.residue_singular_of_model,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed,
    ``DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_lt_one_of_dvd,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_fixed_of_unit_square]
  let regression : Array Name := #[``FreyCriticalCentreTest.curve_invariants,
    ``FreyCriticalCentreTest.exists_centre_at_three,
    ``FreyCriticalCentreTest.centre_residue_singular,
    ``FreyCriticalCentreTest.candidateCurve,
    ``FreyCriticalCentreTest.candidate_identities,
    ``FreyCriticalCentreTest.candidate_boundary_at_three,
    ``FreyCriticalCentreTest.two_not_unit_at_two,
    ``FreyCriticalCentreTest.source37_centre]
  for root in production ++ regression do
    for ax in ← Lean.collectAxioms root do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo m!"PASS: {production.size} production and {regression.size} regression declarations; standard logical axioms only."
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_mul_opposite #[``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_at_centre,
    ``WeierstrassCurve.c_relation] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.translated_defect_factor #[``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.translated_defect] true true
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.exists_criticalCentre #[``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_mul_opposite,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.defect_sub_opposite,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.c4_mul_centreX] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.node_square #[``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.derivative_relation,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.node_square_sub_c4] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.residue_singular #[``DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra.map_equationDefect,
    ``IsLocalRing.residue_eq_zero_iff] true false
  checkRoot ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_fixed_of_unit_square,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.inertia_apply_sub_mem_nonunits,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.node_square] true false
  checkRoot ``DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime #[``DkMath.Lib.NumberTheory.EllipticCriticalCentre.exists_criticalCentre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed,
    ``DkMath.FLT.Frey.Source.curve_discriminant_ne_zero,
    ``DkMath.FLT.Frey.Source.valuation_c4_eq_one,
    ``DkMath.FLT.Frey.Source.valuation_discriminant_pth_power] false false
  checkRoot ``FreyCriticalCentreTest.exists_centre_at_three #[``DkMath.Lib.NumberTheory.EllipticCriticalCentre.exists_criticalCentre,
    ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed] true false
  checkRoot ``FreyCriticalCentreTest.centre_residue_singular #[``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.residue_singular_of_model] true false
  checkRoot ``FreyCriticalCentreTest.candidate_boundary_at_three #[``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_lt_one_of_dvd,
    ``DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd] true false
  checkRoot ``FreyCriticalCentreTest.source37_centre #[``DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime] false false
  checkInputs ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.exists_criticalCentre #[`h₁, `h₂, `h₃, `h₄, `h₆, `hΔ, `hvΔ, `hc₄] #[`hcentre, `hfix, `hσv, `hcases, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed #[`C, `E, `A, `h2, `σ, `hσ] #[`hfix, `hσv, `hcases, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime #[`S, `hp, `hq2, `hd, `A, `hA] #[`hcentre, `hfix, `hσv, `hcases, `hno, `hqp]

#print axioms DkMath.Lib.NumberTheory.EllipticCriticalCentre.exists_criticalCentre
#print axioms DkMath.Lib.NumberTheory.EllipticCriticalCentre.CriticalCentre.inertia_fixed
#print axioms DkMath.FLT.Frey.Source.exists_criticalCentre_at_bad_prime
#print axioms FreyCriticalCentreTest.exists_centre_at_three
#print axioms FreyCriticalCentreTest.candidate_boundary_at_three

end Note031CriticalCentreDependencyAudit
