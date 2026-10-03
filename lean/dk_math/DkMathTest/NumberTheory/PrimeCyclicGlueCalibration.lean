/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimeCyclicGlue
import Mathlib.Tactic.NormNum

#print "file: DkMathTest.NumberTheory.PrimeCyclicGlueCalibration"

namespace DkMathTest.PrimeCyclicGlue

open Polynomial DkMath.NumberTheory

/-- The smallest prime is included; augmentation 3 and cyclotomic class X agree mod 2. -/
theorem prime_two_reconstruction :
    ∃ f : ℤ[X], f.eval 1 = 3 ∧ cyclotomic 2 ℤ ∣ f - X := by
  apply (exists_polynomial_prime_glue_iff 2 3 X).mpr
  norm_num

/-- A second prime, with a nonconstant supplied component. -/
theorem prime_three_reconstruction :
    ∃ f : ℤ[X], f.eval 1 = 4 ∧
      AdjoinRoot.mk (cyclotomic 3 ℤ) f = AdjoinRoot.mk (cyclotomic 3 ℤ) X := by
  apply (exists_prime_cyclic_glue_iff 3 4 _).mpr
  rw [primeCyclotomicResidue_mk]
  rw [eval_X]
  decide

/-- Erasing the common residue condition would admit this impossible pair. -/
theorem incompatible_pair :
    ¬ ∃ f : ℤ[X], f.eval 1 = 2 ∧ cyclotomic 3 ℤ ∣ f - X := by
  rw [exists_polynomial_prime_glue_iff]
  norm_num

/-- The correcting polynomial has the requested components in the existing cyclic quotient. -/
example : aksQuotientMap ℤ 3 (X + cyclotomic 3 ℤ) =
    aksQuotientMap ℤ 3 (X + cyclotomic 3 ℤ + (X ^ 3 - 1)) := by
  apply (aks_prime_cyclic_glue_eq_iff 3 _ _).mpr
  constructor
  · simp
  · apply AdjoinRoot.mk_eq_mk.mpr
    have hd : cyclotomic 3 ℤ ∣ (X ^ 3 - 1 : ℤ[X]) := by
      rw [← cyclotomic_prime_mul_X_sub_one ℤ 3]
      exact dvd_mul_right _ _
    convert dvd_neg.mpr hd using 1
    ring

/-- Genuine cube components reconstruct a genuine cube, even when the input
representative includes an arbitrary cyclic-ideal correction. -/
theorem genuine_cube (q t : ℤ[X]) :
    ∃ root : AKSCyclicQuotient ℤ 3,
      aksQuotientMap ℤ 3 (q ^ 3 + (X ^ 3 - 1) * t) = root ^ 3 := by
  apply aks_prime_cyclic_is_pow_of_components 3 _ (q.eval 1)
    (AdjoinRoot.mk (cyclotomic 3 ℤ) q)
  · simp
  · have hz : AdjoinRoot.mk (cyclotomic 3 ℤ) (X ^ 3 - 1) = 0 := by
      apply AdjoinRoot.mk_eq_zero.mpr
      rw [← cyclotomic_prime_mul_X_sub_one ℤ 3]
      exact dvd_mul_right _ _
    rw [map_add, map_mul, hz, zero_mul, add_zero, map_pow]

/-- Composite length has a different common modulus: Phi_4(1)=2, not 4. -/
theorem composite_boundary :
    ∃ f : ℤ[X], f.eval 1 = 2 ∧ cyclotomic 4 ℤ ∣ f := by
  refine ⟨cyclotomic 4 ℤ, ?_, dvd_refl _⟩
  exact eval_one_cyclotomic_prime_pow (R := ℤ) (p := 2) 1

example : ¬ (4 : ℤ) ∣ 2 := by norm_num

end DkMathTest.PrimeCyclicGlue
