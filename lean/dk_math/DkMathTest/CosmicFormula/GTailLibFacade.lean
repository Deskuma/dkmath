/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib

#print "file: DkMathTest.CosmicFormula.GTailLibFacade"

/-! Public Lib import smoke tests. Each example consumes an existing endpoint. -/

namespace DkMathTest.CosmicFormula.GTailLibFacade

open DkMath.CosmicFormula

example {R : Type*} [CommSemiring R] (d : ℕ) (S : Finset ℕ) (x u : R) :
    (x + u) ^ d = selectedGap d S x u + selectedBody d S x u :=
  selectedGap_add_selectedBody d S x u

example {R : Type*} [CommSemiring R] (d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R)
    (hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    selectedBody d S x u = x ^ i * u ^ (d - j) * selectedResidual d S i j x u :=
  selectedBody_eq_monomial_mul_residual d S i j x u hij hjd hbounds

example (p : ℕ) (hp : Nat.Prime p) : coeffGCD p (Finset.Ico 1 p) = p :=
  coeffGCD_prime_interior p hp

example (p x u : ℕ) (hp : Nat.Prime p) :
    p * x * u ∣ selectedBody p (Finset.Ico 1 p) x u :=
  prime_mul_coords_dvd_selectedBody_interior p x u hp

example (d : ℕ) (S T : Finset ℕ) (x u m : ℕ)
    (hterms : ∀ k ∈ (activeSelectedIndices d T \ activeSelectedIndices d S) ∪
        (activeSelectedIndices d S \ activeSelectedIndices d T), m ∣ selectedTerm d k x u) :
    Nat.ModEq m (selectedBody d S x u) (selectedBody d T x u) ∧
      Nat.ModEq m (selectedGap d S x u) (selectedGap d T x u) :=
  selected_modEq_of_dvd_moved d S T x u m hterms

example {R : Type*} [CommSemiring R] (x u : R) :
    (x + u) ^ 7 = (u ^ 7 + x ^ 7) +
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 :=
  add_pow_seven_eq_gap_add_interior x u

example {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2) :=
  coprime_product_seven_quadratic hcop

example : 7 ∣ GTail 7 1 14 (2 : ℕ) ∧ ¬ 7 ^ 2 ∣ GTail 7 1 14 (2 : ℕ) :=
  gtail_seven_exact_seven_layer (by norm_num) (by norm_num)

#print axioms selectedGap_add_selectedBody
#print axioms selectedBody_eq_monomial_mul_residual
#print axioms coeffGCD_prime_interior
#print axioms prime_mul_coords_dvd_selectedBody_interior
#print axioms selected_modEq_of_dvd_moved
#print axioms add_pow_seven_eq_gap_add_interior
#print axioms coprime_product_seven_quadratic
#print axioms gtail_seven_exact_seven_layer

end DkMathTest.CosmicFormula.GTailLibFacade
