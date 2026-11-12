/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTailKernelVanishing

#print "file: DkMathTest.FLT.InertiaTailKernelVanishing"

namespace InertiaTailKernelVanishingTest
open DkMath.Lib.NumberTheory DkMath.Lib.NumberTheory.InertiaResidue
open DkMath.Lib.NumberTheory.ValuationInertia
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

-- Both root and target remain in the same actual tail-fixing subgroup; not just its closure.
example (n : ℕ) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hg : g ∈ (tailField A p q).fixingSubgroup) :
    ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      w ∈ inertiaSubgroupIn A ℚ ∧ w ∈ (tailField A p q).fixingSubgroup ∧ w ^ (p ^ n) = g :=
  tailFixing_inertia_pRoot hp hq hpq A hA n g hg

-- No finite-index, power-root, or cyclicity provider is needed at the actual endpoint.
example {H : Type*} [Group H] (f : inertiaSubgroupIn A ℚ →* H)
    (n : ℕ) (hexp : ∀ h : H, h ^ (p ^ n) = 1) (g : inertiaSubgroupIn A ℚ)
    (hr : ∀ α k, α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α) : f g = 1 :=
  allRadicals_map_eq_one hp hq hpq A hA f n hexp g hr

-- Without the prime-to-p order condition, the cube map of a finite group can fail.
example : ¬ ∃ w : Equiv.Perm (Fin 3),
    w ^ 3 = Equiv.swap 0 1 * Equiv.swap 1 2 := by decide

-- Fixing a first quotient does not imply vanishing in a deeper quotient.
example : (ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)) (3 : ZMod 9) = 0 ∧
    (3 : ZMod 9) ≠ 0 := by decide
end InertiaTailKernelVanishingTest

#print axioms DkMath.Lib.NumberTheory.InertiaClosed.fixedField_topologicalClosure_eq
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.fixingSubgroup_fixedField_eq_topologicalClosure
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.exists_mem_apply_eq_of_mem_fixingSubgroup
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.isOpen_setOf_apply
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.isClosed_setOf_apply
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.mem_inertia_map_iff
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.isClosed_inertia_map
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.topologicalClosure_inertia_map
#print axioms DkMath.Lib.NumberTheory.InertiaClosed.fixingSubgroup_fixedField_inertia
#print axioms DkMath.Lib.NumberTheory.KummerPrimeQuotient.index_coprime_of_forall_pow_surjective
#print axioms DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.eq_one_of_forall_mem_openNormalSubgroup
#print axioms DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.exists_pow_mul_inv_mem
#print axioms DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots.exists_pow_pow_eq
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailIntermediate_exact_pRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailField_primitiveRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailGalois_index_coprime
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailFixing_inertia_pRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.mem_tailFixing_iff_all_radicals
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_inertia_pRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.allRadicals_map_eq_one
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_commonProjection_eq_one
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_evaluations_eq_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.allRadicals_fixed_differences_eq_one
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.tailFixing_le_commonProjection_kernel
