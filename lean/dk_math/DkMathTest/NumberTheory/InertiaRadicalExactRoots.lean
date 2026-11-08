/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalExactRoots

#print "file: DkMathTest.NumberTheory.InertiaRadicalExactRoots"

namespace InertiaRadicalExactRootsTest
open DkMath.Lib.NumberTheory DkMath.Lib.NumberTheory.InertiaResidue
open DkMath.Lib.NumberTheory.ValuationInertia
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)

-- Compile the actual endpoints with no stability, Henselian, residue, or root provider.
example : HenselianLocalRing (A.comap (algebraMap E (AlgebraicClosure ℚ))) :=
  StableValuation.overfield_henselian A E ((fixedField_le_tailField A p q).trans hE)

example (u : A.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ w : A.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit w ∧ w ^ p = u :=
  exact_unit_pRoot hp hq hpq A hA E ((fixedField_le_tailField A p q).trans hE) u hu

-- Nonzero target => nonzero root, at every finite depth in the same actual E.
example (n : ℕ) (a : E) (ha : a ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ b ^ (p ^ n) = a := by
  obtain ⟨b, hb⟩ := tailOverfield_primePower_surjective hp hq hpq A hA E hE n a
  refine ⟨b, ?_, hb⟩
  intro hzero
  rw [hzero, zero_pow (pow_ne_zero _ hp.ne_zero)] at hb
  exact ha hb.symm

example : ∃ b : tailField A p q, b ^ p = 0 :=
  tailOverfield_power_surjective hp hq hpq A hA _ le_rfl 0

-- Value divisibility requires roots in the same field: rational valuation values need not be squares.
example : ¬ ∃ n : ℤ, 2 * n = 1 := by omega
end InertiaRadicalExactRootsTest

#print axioms DkMath.Lib.NumberTheory.InertiaStability.isClosed_apply_mem
#print axioms DkMath.Lib.NumberTheory.InertiaStability.isClosed_decompositionSubgroup
#print axioms DkMath.Lib.NumberTheory.InertiaStability.fixingSubgroup_fixedField_map_inertia_le
#print axioms DkMath.Lib.NumberTheory.InertiaStability.smul_eq_self_of_mem_fixingSubgroup
#print axioms DkMath.Lib.NumberTheory.InertiaStability.overfield_stable
#print axioms DkMath.Lib.NumberTheory.StableValuation.isUnit_iff_inv_mem
#print axioms DkMath.Lib.NumberTheory.StableValuation.mem_maximalIdeal_iff
#print axioms DkMath.Lib.NumberTheory.StableValuation.mem_maximalIdeal_iff_map
#print axioms DkMath.Lib.NumberTheory.StableValuation.hensel_of_stable
#print axioms DkMath.Lib.NumberTheory.StableValuation.henselianLocalRing_comap
#print axioms DkMath.Lib.NumberTheory.StableValuation.overfield_henselian
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.exists_pow_eq_of_pow_sub_mem
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.prime_isUnit_comap
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.exact_unit_pRoot
#print axioms DkMath.Lib.NumberTheory.RationalValue.valuation_natCast_eq_one
#print axioms DkMath.Lib.NumberTheory.RationalValue.valuation_intCast
#print axioms DkMath.Lib.NumberTheory.RationalValue.valuation_ratCast
#print axioms DkMath.Lib.NumberTheory.RationalValue.exists_valuation_pow_eq
#print axioms DkMath.Lib.NumberTheory.RadicalValue.eq_one_of_pow_eq_one
#print axioms DkMath.Lib.NumberTheory.RadicalValue.exists_valuation_eq_pow
#print axioms DkMath.Lib.NumberTheory.RadicalDescent.exists_pow_eq
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_exact_pRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailField_exact_pRoot
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_power_surjective
#print axioms DkMath.Lib.NumberTheory.InertiaResidue.tailOverfield_primePower_surjective
