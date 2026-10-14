/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Zsigmondy
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.ZsigmondyCyclotomicNoLift
import DkMath.NumberTheory.PrimitiveSet.Basic
import DkMath.NumberTheory.Primitive.PrimitiveConservationKernel
import DkMath.NumberTheory.StructuralArithmetic.GNBridge

#print "file: GapFocusingSuccessorPrimitiveAudit002"

/-! Adjacent GN support separation does not imply first occurrence among all
earlier degrees. The standard base-two degree-six obstruction is checked
against the actual production GN and primitive-prime definitions. -/

namespace GapFocusingSuccessorPrimitiveAudit002

open DkMath.Zsigmondy
open DkMath.CosmicFormulaBinom

theorem adjacent_base_two_values :
    GN 5 (1 : ℕ) 1 = 31 ∧ GN 6 (1 : ℕ) 1 = 63 := by
  decide

theorem adjacent_base_two_coprime :
    Nat.Coprime (GN 5 (1 : ℕ) 1) (GN 6 (1 : ℕ) 1) := by
  decide

theorem degree_six_prime_divisor_already_appeared {q : ℕ}
    (hq : Nat.Prime q) (hdiv : q ∣ (2 : ℕ) ^ 6 - 1 ^ 6) :
    q ∣ (2 : ℕ) ^ 2 - 1 ^ 2 ∨ q ∣ (2 : ℕ) ^ 3 - 1 ^ 3 := by
  have hfactor : q ∣ (3 : ℕ) ^ 2 * 7 := by simpa using hdiv
  rcases hq.dvd_mul.mp hfactor with hthree | hseven
  · left
    simpa using hq.dvd_of_dvd_pow hthree
  · right
    simpa using hseven

theorem no_primitive_prime_base_two_degree_six :
    ¬ ∃ q, PrimitivePrimeDivisor 2 1 6 q := by
  rintro ⟨q, hq⟩
  rcases degree_six_prime_divisor_already_appeared hq.prime hq.dvd with htwo | hthree
  · exact hq.not_dvd_lower (m := 2) (by decide) (by decide) htwo
  · exact hq.not_dvd_lower (m := 3) (by decide) (by decide) hthree

/-- Missing the actual production odd-prime theorem's extra boundary hypothesis
does not itself mean a primitive prime is absent: `(a,b,d)=(4,1,3)` has `q=7`. -/
theorem production_boundary_hypothesis_not_necessary :
    (3 : ℕ) ∣ 4 - 1 ∧ PrimitivePrimeDivisor 4 1 3 7 := by
  constructor
  · decide
  · refine ⟨by decide, by decide, ?_⟩
    intro m hmpos hmlt
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl <;> decide

#print axioms adjacent_base_two_values
#print axioms adjacent_base_two_coprime
#print axioms degree_six_prime_divisor_already_appeared
#print axioms no_primitive_prime_base_two_degree_six
#print axioms production_boundary_hypothesis_not_necessary
#print axioms DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp
#print axioms DkMath.Zsigmondy.exists_primitivePrimeDivisor_kernel_nat
#print axioms DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
#print axioms DkMath.NumberTheory.PrimitiveBeam.exists_primitive_prime_factor_as_prop
#print axioms DkMath.NumberTheory.PrimitiveBeam.primitive_prime_dvd_GN_body
#print axioms DkMath.NumberTheory.GcdNext.cyclotomic_eval_divides
#print axioms DkMath.NumberTheory.GcdNext.cyclotomic_squarefree
#print axioms DkMath.NumberTheory.GcdNext.noLift_GN_of_primitive_prime_factor_is_false
#print axioms DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
#print axioms DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one_research
#print axioms DkMath.NumberTheory.PrimitiveBeam.primitive_prime_obstructs_GN_perfect_power_research
#print axioms DkMath.NumberTheory.Primitive.primitiveConservationKernel_dichotomy_of_le_fine_squareBody
#print axioms DkMath.NumberTheory.StructuralArithmetic.freshPrimeDirection_GN_of_primitivePrimeFactor

end GapFocusingSuccessorPrimitiveAudit002
