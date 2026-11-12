/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalKernelComparison
import DkMath.Lib.NumberTheory.InertiaRadicalTailField

#print "file: DkMathTest.FLT.Note032FreyTailDependencyAudit"

namespace Note032FreyTailDependencyAudit

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
-- Traverse checked types, constructors and opaque values for all twenty-five roots.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_coset]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_evaluations #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations, ``DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_fixed_differences #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences, ``DkMath.Lib.NumberTheory.InertiaRadical.character_eq_one_iff_root_fixed]
  checkRoot ``DkMath.Lib.NumberTheory.AlgebraicResidue.power_surjective #[``IsAlgClosed.exists_pow_nat_eq]
  checkRoot ``DkMath.Lib.NumberTheory.AlgebraicResidue.nonzero_finite_order #[``Polynomial.isPrimitive_primPart, ``Algebra.IsAlgebraic.isAlgebraic]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.eq_of_pow_eq_one_of_sub_mem #[``geom_sum₂_mul]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.root_mem #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot #[``DkMath.Lib.NumberTheory.InertiaResidue.root_mem]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_pow #[``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_injective #[``DkMath.Lib.NumberTheory.InertiaResidue.eq_of_pow_eq_one_of_sub_mem]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.exists_root_lift #[``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_injective, ``Polynomial.card_nthRoots]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField #[``DkMath.Lib.NumberTheory.ValuationInertia.inertiaSubgroupIn]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.primePower_root_lift #[``DkMath.Lib.NumberTheory.InertiaResidue.exists_root_lift, ``HasEnoughRootsOfUnity.exists_primitiveRoot, ``DkMath.Lib.NumberTheory.InertiaRadical.inertia_fixes_primePower_root]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot #[``DkMath.Lib.NumberTheory.AlgebraicResidue.power_surjective, ``DkMath.Lib.NumberTheory.AlgebraicResidue.nonzero_finite_order, ``DkMath.Lib.NumberTheory.InertiaResidue.primePower_root_lift]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot_isUnit #[``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.radicals #[]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailField #[``DkMath.Lib.NumberTheory.InertiaResidue.fixedField, ``DkMath.Lib.NumberTheory.InertiaResidue.radicals]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField_le_tailField #[``DkMath.Lib.NumberTheory.InertiaResidue.tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.radical_mem_tailField #[``DkMath.Lib.NumberTheory.InertiaResidue.tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tower_mem_tailField #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_pow, ``DkMath.Lib.NumberTheory.InertiaResidue.radical_mem_tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.compatible_roots_in_tailField #[``DkMath.Lib.NumberTheory.PrimeRadicalTower.tower_compat, ``DkMath.Lib.NumberTheory.InertiaResidue.tower_mem_tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_primePower_root_lifts #[``DkMath.Lib.NumberTheory.InertiaResidue.primePower_root_lift, ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField_le_tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_unit_roots #[``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot_isUnit, ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField_le_tailField]
  checkRoot ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_unit_roots #[``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot_isUnit, ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField_le_tailField]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_evaluations #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_fixed_differences #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.AlgebraicResidue.power_surjective #[`P, `n, `hn, `c] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.AlgebraicResidue.nonzero_finite_order #[`P, `q, `hqp, `hA, `c, `hc] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.eq_of_pow_eq_one_of_sub_mem #[`hm, `hmu, `x, `y, `hx, `hy, `hxy] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.root_mem #[`A, `hm, `hμ] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot #[`A, `hm, `ζ, `hζ] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_pow #[`A, `hm, `ζ, `hζ] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_injective #[`A, `hm, `hmu, `hres] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.exists_root_lift #[`A, `hm, `hmu, `ζ₀, `hζ₀, `η, `hη] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField #[`A] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.primePower_root_lift #[`hp, `hq, `hpq, `A, `hA, `i, `y, `hy] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot #[`hp, `hq, `hpq, `P, `hA, `E, `hE, `u, `hu] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot_isUnit #[`hp, `hq, `hpq, `P, `hA, `E, `hE, `u, `hu] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.radicals #[`p, `q] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailField #[`A, `p, `q] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.fixedField_le_tailField #[`A, `p, `q] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.radical_mem_tailField #[`A, `hz] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tower_mem_tailField #[`A, `hp, `n] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.compatible_roots_in_tailField #[`A, `hp] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_primePower_root_lifts #[`hp, `hq, `hpq, `A, `hA, `i, `y, `hy] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailField_unit_roots #[`hp, `hq, `hpq, `A, `hA, `u, `hu] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]
  checkInputs ``DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_unit_roots #[`hp, `hq, `hpq, `A, `hA, `E, `hE, `u, `hu] #[`hgen, `hcyclic, `htail, `hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hinj, `hcompare, `hcontain, `hroots, `htor, `hlifts, `hresidue, `hhenselian, `hclass, `hcofixed]

end Note032FreyTailDependencyAudit
