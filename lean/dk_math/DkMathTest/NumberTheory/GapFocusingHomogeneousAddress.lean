/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.HomogeneousAddress
import DkMath.NumberTheory.GapFocusing.CyclotomicBoundary
import DkMath.NumberTheory.GapFocusing.Support

#print "file: DkMathTest.NumberTheory.GapFocusingHomogeneousAddress"

namespace DkMathTest.NumberTheory.GapFocusingHomogeneousAddress

open DkMath.NumberTheory.GapFocusing DkMath.CFBRC Polynomial

/-- The same integer prime occurs in two different actual homogeneous layers. -/
theorem homogeneous_two_six_values :
    cyclotomicShiftedEval 2 (1 : ℤ) 1 = 3 ∧
      cyclotomicShiftedEval 6 (1 : ℤ) 1 = 3 := by
  simp only [cyclotomicShiftedEval_one_eq_cyclotomicEval]
  norm_num [cyclotomicEval, eval₂_eq_eval_map, cyclotomic_two, cyclotomic_six]

/-- The other degree-six divisor layer carries the prime seven. -/
example : cyclotomicShiftedEval 3 (1 : ℤ) 1 = 7 := by
  rw [cyclotomicShiftedEval_one_eq_cyclotomicEval]
  norm_num [cyclotomicEval, eval₂_eq_eval_map, cyclotomic_three]

/-- In characteristic three, the sixth layer becomes the square of the
second layer. This is a polynomial identity behind the shared prime support. -/
theorem degree_six_mod_three_repeated_layer :
    cyclotomic 6 (ZMod 3) = cyclotomic 2 (ZMod 3) ^ 2 := by
  simpa using (cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod 3)
    (p := 3) (n := 2) (by decide))

/-- The evaluated support map itself fails injectivity, not merely disjointness. -/
theorem layerPrimeSupport_not_injective :
    ¬ Function.Injective (layerPrimeSupport (2 : ℤ) 1) := by
  intro hinj
  have heq : layerPrimeSupport (2 : ℤ) 1 2 = layerPrimeSupport (2 : ℤ) 1 6 := by
    ext q
    change (q.Prime ∧ (q : ℤ) ∣ cyclotomicShiftedEval 2 (1 : ℤ) 1) ↔
      (q.Prime ∧ (q : ℤ) ∣ cyclotomicShiftedEval 6 (1 : ℤ) 1)
    rw [homogeneous_two_six_values.1, homogeneous_two_six_values.2]
  have h := hinj heq
  norm_num at h

/-- Omitting degree one creates a first nontrivial address that is not primitive. -/
theorem order_one_address_not_primitive :
    IsLeast (primeLayerAddresses 3 (4 : ℤ) 1) 3 ∧
      ¬ DkMath.Zsigmondy.PrimitivePrimeDivisor 4 1 3 3 := by
  constructor
  · apply primeLayerAddresses_isLeast_of_primeOrder_eq_one 3 4 1 (by norm_num)
    have hratio : primeRatio 3 4 1 = 1 := by
      change (4 : ZMod 3) * 1⁻¹ = 1
      simpa using (by decide : (4 : ZMod 3) = 1)
    simp [primeOrder, hratio]
  · intro h
    exact h.not_dvd_lower (m := 1) (by decide) (by decide) (by decide)

/-- A positive primitive example is also a genuine first homogeneous layer. -/
theorem first_layer_primitive_example : FirstLayerAppearance 3 (2 : ℤ) 1 2 := by
  apply primitivePrimeDivisor_firstLayerAppearance (by decide) (by decide)
  refine ⟨by decide, by decide, ?_⟩
  intro m hm hmlt
  have : m = 1 := by omega
  subst m
  decide

/-- Degree-six successor freshness still allows both prime supports to have
already appeared, despite different formal layer indices. -/
theorem degree_six_fresh_not_global :
    ¬(3 : ℕ) ∣ DkMath.CosmicFormula.GTail 5 1 1 1 ∧
      ¬(7 : ℕ) ∣ DkMath.CosmicFormula.GTail 5 1 1 1 ∧
      ¬ DkMath.Zsigmondy.PrimitivePrimeDivisor 2 1 6 3 ∧
      ¬ DkMath.Zsigmondy.PrimitivePrimeDivisor 2 1 6 7 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro h
    exact h.not_dvd_lower (m := 2) (by decide) (by decide) (by decide)
  · intro h
    exact h.not_dvd_lower (m := 3) (by decide) (by decide) (by decide)

/-- Every prime divisor at degree six was already present at degree two or three. -/
theorem no_primitive_prime_base_two_degree_six :
    ¬ ∃ q, DkMath.Zsigmondy.PrimitivePrimeDivisor 2 1 6 q := by
  rintro ⟨q, h⟩
  have hfactor : q ∣ (3 : ℕ) ^ 2 * 7 := by simpa using h.dvd
  rcases h.prime.dvd_mul.mp hfactor with hthree | hseven
  · apply h.not_dvd_lower (m := 2) (by decide) (by decide)
    simpa using h.prime.dvd_of_dvd_pow hthree
  · apply h.not_dvd_lower (m := 3) (by decide) (by decide)
    simpa using hseven

/-- Primes dividing just one coordinate have no addresses, while a shared
coordinate prime appears at every nontrivial homogeneous degree. -/
theorem coordinate_boundary_addresses :
    primeLayerAddresses 3 (2 : ℤ) 3 = ∅ ∧
      primeLayerAddresses 3 (3 : ℤ) 2 = ∅ ∧
      primeLayerAddresses 3 (6 : ℤ) 3 = {n | 1 < n} := by
  refine ⟨primeLayerAddresses_eq_empty_of_dvd_second 3 2 3 (by norm_num) (by norm_num),
    primeLayerAddresses_eq_empty_of_dvd_first 3 3 2 (by norm_num) (by norm_num),
    primeLayerAddresses_eq_nontrivial_of_dvd_coordinates 3 6 3 (by norm_num) (by norm_num)⟩

#print axioms homogeneous_two_six_values
#print axioms degree_six_mod_three_repeated_layer
#print axioms layerPrimeSupport_not_injective
#print axioms order_one_address_not_primitive
#print axioms first_layer_primitive_example
#print axioms degree_six_fresh_not_global
#print axioms no_primitive_prime_base_two_degree_six
#print axioms coordinate_boundary_addresses

end DkMathTest.NumberTheory.GapFocusingHomogeneousAddress
