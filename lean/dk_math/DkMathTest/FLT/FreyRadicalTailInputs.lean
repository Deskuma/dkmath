/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalKernelComparison
import DkMath.Lib.NumberTheory.InertiaRadicalTailField

#print "file: DkMathTest.FLT.FreyRadicalTailInputs"

namespace FreyRadicalTailInputsTest
abbrev B := ZMod 9
private def red : B →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)

-- Unit inputs and approximate root can all be genuine, without the chosen root exact.
example : IsUnit (4 : B) := ⟨⟨4, 7, by decide, by decide⟩, rfl⟩
example : IsUnit (1 : B) := isUnit_one
example : (1 : B) ^ 2 - 4 ∈ Ideal.span ({3} : Set B) := by
  apply Ideal.mem_span_singleton.mpr
  exact ⟨2, by decide⟩
example : (1 : B) ^ 2 ≠ 4 := by decide
example : red ((1 : B) ^ 2) = red 4 := by decide

-- Unit exponent2: reduction separates roots of unity. Nonunit exponent3: it fails.
example : ∀ x y : B, x ^ 2 = 1 → y ^ 2 = 1 → red x = red y → x = y := by decide
example : (1 : B) ^ 3 = 1 ∧ (4 : B) ^ 3 = 1 ∧ red 1 = red 4 ∧ (1 : B) ≠ 4 := by decide

-- The known root kernel and the common kernel are still distinct arithmetic targets.
private def first : (ZMod 5 × ZMod 5) →ₗ[ZMod 5] ZMod 5 := LinearMap.fst _ _ _
private def second : (ZMod 5 × ZMod 5) →ₗ[ZMod 5] ZMod 5 := LinearMap.snd _ _ _
example : ¬ LinearMap.ker first ≤ LinearMap.ker second := by
  intro hi
  have he := hi (show ((0, 1) : ZMod 5 × ZMod 5) ∈ LinearMap.ker first from rfl)
  exact (by decide : (1 : ZMod 5) ≠ 0) he
end FreyRadicalTailInputsTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_evaluations
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_comparison_iff_fixed_differences
#print axioms DkMath.Lib.NumberTheory.AlgebraicResidue.power_surjective
#print axioms DkMath.Lib.NumberTheory.AlgebraicResidue.nonzero_finite_order
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.eq_of_pow_eq_one_of_sub_mem
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.root_mem
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.residueRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_pow
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.residueRoot_injective
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.exists_root_lift
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.fixedField
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.primePower_root_lift
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.approximate_unit_pRoot_isUnit
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.radicals
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailField
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.fixedField_le_tailField
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.radical_mem_tailField
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tower_mem_tailField
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.compatible_roots_in_tailField
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailField_primePower_root_lifts
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailField_unit_roots
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_unit_roots
