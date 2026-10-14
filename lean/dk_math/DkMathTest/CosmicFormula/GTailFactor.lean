/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailFactor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

#print "file: DkMathTest.CosmicFormula.GTailFactor"

/-!
# Regression tests for selective monomial factors and coefficient gcd

Sparse selections, endpoints, empty and degree-zero bodies, out-of-range
indices, and prime interiors are checked independently of FLT. All algebraic
examples use a general commutative semiring. All public theorems are audited.
-/

open scoped BigOperators

namespace DkMathTest.GTailFactor

open DkMath.CosmicFormula

variable {R : Type*} [CommSemiring R]

-- The sparse degree-five equality is obtained from the bound factor theorem.
example (x u : R) :
    selectedBody 5 {1, 3} x u = x * u ^ 2 * (5 * u ^ 2 + 10 * x ^ 2) := by
  have hbounds : ∀ k ∈ activeSelectedIndices 5 {1, 3}, 1 ≤ k ∧ k ≤ 3 := by
    intro k hk
    simp only [mem_activeSelectedIndices, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have hres : selectedResidual 5 {1, 3} 1 3 x u = 5 * u ^ 2 + 10 * x ^ 2 := by
    norm_num [selectedResidual, activeSelectedIndices, Finset.sum_filter,
      Finset.sum_range_succ, Nat.choose]
  simpa only [hres, pow_one, show 5 - 3 = 2 from rfl] using
    selectedBody_eq_monomial_mul_residual 5 {1, 3} 1 3 x u (by decide) (by decide) hbounds

-- The extrema are computed from active indices, not from the raw selection.
example (x u : R) :
    selectedBody 3 {1, 100} x u = x * u ^ 2 * (3 : R) := by
  have hactive : activeSelectedIndices 3 {1, 100} = {1} := by decide
  have hbounds : ∀ k ∈ activeSelectedIndices 3 {1, 100}, 1 ≤ k ∧ k ≤ 1 := by
    rw [hactive]
    simp
  have hres : selectedResidual 3 {1, 100} 1 1 x u = 3 := by
    simp [selectedResidual, hactive]
  simpa only [hres, pow_one, show 3 - 1 = 2 from rfl] using
    selectedBody_eq_monomial_mul_residual 3 {1, 100} 1 1 x u
      le_rfl (by decide) hbounds

example (x u : R) :
    selectedBody 5 {1, 3} x u =
      x ^ (activeSelectedIndices 5 {1, 3}).min' (by decide) *
        u ^ (5 - (activeSelectedIndices 5 {1, 3}).max' (by decide)) *
        selectedResidual 5 {1, 3}
          ((activeSelectedIndices 5 {1, 3}).min' (by decide))
          ((activeSelectedIndices 5 {1, 3}).max' (by decide)) x u :=
  selectedBody_eq_min_max_mul_residual 5 {1, 3} x u (by decide)

-- Endpoint coefficients are 1; evaluated endpoint monomials may be larger.
example (d : ℕ) (x u : R) : selectedBody d {0} x u = u ^ d := by
  rw [selectedBody_singleton d 0 x u (Nat.zero_le d)]
  simp [selectedTerm]

example (d : ℕ) (x u : R) : selectedBody d {d} x u = x ^ d := by
  rw [selectedBody_singleton d d x u le_rfl]
  simp [selectedTerm]

example (d : ℕ) : coeffGCD d {0} = 1 :=
  coeffGCD_eq_one_of_zero_mem d {0} (by simp)

example (d : ℕ) : coeffGCD d {d} = 1 :=
  coeffGCD_eq_one_of_self_mem d {d} (by simp)

example (d : ℕ) : coeffGCD d {0, d} = 1 :=
  coeffGCD_eq_one_of_zero_mem d {0, d} (by simp)

-- Empty and degree-zero cases, including empty active sets from nonempty input.
example (d i j : ℕ) (x u : R) : selectedResidual d ∅ i j x u = 0 := by
  simp [selectedResidual, activeSelectedIndices]

example (d i j : ℕ) (x u : R) (hij : i ≤ j) (hjd : j ≤ d) :
    selectedBody d ∅ x u = x ^ i * u ^ (d - j) * selectedResidual d ∅ i j x u := by
  apply selectedBody_eq_monomial_mul_residual d ∅ i j x u hij hjd
  simp [activeSelectedIndices]

example (x u : R) : selectedBody 0 {0} x u = 1 := by
  rw [selectedBody_singleton 0 0 x u le_rfl]
  simp [selectedTerm]

example : coeffGCD 0 ∅ = 0 ∧ coeffGCD 0 {0} = 1 ∧ coeffGCD 0 {100} = 0 := by
  simp [coeffGCD, activeSelectedIndices]

example : coeffGCD 3 {1, 100} = 3 := by
  have hactive : activeSelectedIndices 3 {1, 100} = {1} := by decide
  simp [coeffGCD, hactive]

-- Zero coordinates retain the same factor contract without nonvanishing assumptions.
example (u : R) : selectedBody 5 {1, 3} 0 u = 0 := by
  have hbounds : ∀ k ∈ activeSelectedIndices 5 {1, 3}, 1 ≤ k ∧ k ≤ 3 := by
    intro k hk
    simp only [mem_activeSelectedIndices, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  rw [selectedBody_eq_monomial_mul_residual 5 {1, 3} 1 3 0 u
    (by decide) (by decide) hbounds]
  simp

example (x : R) : selectedBody 5 {1, 3} x 0 = 0 := by
  have hbounds : ∀ k ∈ activeSelectedIndices 5 {1, 3}, 1 ≤ k ∧ k ≤ 3 := by
    intro k hk
    simp only [mem_activeSelectedIndices, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  rw [selectedBody_eq_monomial_mul_residual 5 {1, 3} 1 3 x 0
    (by decide) (by decide) hbounds]
  simp

-- Prime interiors: exact coefficient gcd and combined divisor, including p=2.
example : coeffGCD 2 (Finset.Ico 1 2) = 2 :=
  coeffGCD_prime_interior 2 (by decide)

example : coeffGCD 3 (Finset.Ico 1 3) = 3 :=
  coeffGCD_prime_interior 3 (by decide)

example : coeffGCD 7 (Finset.Ico 1 7) = 7 :=
  coeffGCD_prime_interior 7 (by decide)

-- Independent finite gcd computations verify the prime adapters.
example : coeffGCD 3 (Finset.Ico 1 3) = 3 ∧ coeffGCD 7 (Finset.Ico 1 7) = 7 := by
  decide

example (x u : ℕ) : 2 * x * u ∣ selectedBody 2 (Finset.Ico 1 2) x u :=
  prime_mul_coords_dvd_selectedBody_interior 2 x u (by decide)

example (x u : ℕ) : 3 * x * u ∣ selectedBody 3 (Finset.Ico 1 3) x u :=
  prime_mul_coords_dvd_selectedBody_interior 3 x u (by decide)

example (x u : ℕ) : 7 * x * u ∣ selectedBody 7 (Finset.Ico 1 7) x u :=
  prime_mul_coords_dvd_selectedBody_interior 7 x u (by decide)

example (x u : R) : selectedBody 2 (Finset.Ico 1 2) x u = 2 * x * u := by
  norm_num [selectedBody, selectedTerm, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

example (x u : R) : selectedBody 3 (Finset.Ico 1 3) x u = 3 * x * u * (x + u) := by
  have hbody : selectedBody 3 (Finset.Ico 1 3) x u = 3 * x * u ^ 2 + 3 * x ^ 2 * u := by
    norm_num [selectedBody, selectedTerm, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]
  rw [hbody]
  ring

-- A sparse prime interior still has prime content when coefficient p is retained.
example : coeffGCD 7 {1, 4, 100} = 7 := by
  apply coeffGCD_eq_prime_of_interior 7 {1, 4, 100} (by decide)
  · intro k hk
    simp only [mem_activeSelectedIndices, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  · simp

-- Coefficient content is not the evaluated natural Body itself.
example : coeffGCD 3 (Finset.Ico 1 3) = 3 ∧ selectedBody 3 (Finset.Ico 1 3) 1 1 = (6 : ℕ) := by
  decide

end DkMathTest.GTailFactor

#print axioms DkMath.CosmicFormula.mem_activeSelectedIndices
#print axioms DkMath.CosmicFormula.selectedBody_eq_monomial_mul_residual
#print axioms DkMath.CosmicFormula.selectedBody_eq_min_max_mul_residual
#print axioms DkMath.CosmicFormula.monomial_dvd_selectedBody
#print axioms DkMath.CosmicFormula.coeffGCD_empty
#print axioms DkMath.CosmicFormula.coeffGCD_dvd_choose
#print axioms DkMath.CosmicFormula.dvd_coeffGCD_iff
#print axioms DkMath.CosmicFormula.dvd_selectedResidual_of_dvd_coeff
#print axioms DkMath.CosmicFormula.coeffGCD_dvd_selectedBody
#print axioms DkMath.CosmicFormula.coeffGCD_eq_one_of_zero_mem
#print axioms DkMath.CosmicFormula.coeffGCD_eq_one_of_self_mem
#print axioms DkMath.CosmicFormula.coeffGCD_mul_monomial_dvd_selectedBody
#print axioms DkMath.CosmicFormula.activeSelectedIndices_interior
#print axioms DkMath.CosmicFormula.coeffGCD_eq_prime_of_interior
#print axioms DkMath.CosmicFormula.coeffGCD_prime_interior
#print axioms DkMath.CosmicFormula.prime_mul_coords_dvd_selectedBody_interior
