/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSelection
import Mathlib.Tactic.Ring

#print "file: DkMathTest.CosmicFormula.GTailSelection"

/-!
# Regression tests for selective binomial balance

These examples check degree-three and degree-seven selections and boundary
cases over a general commutative semiring. The final commands audit all
exported selection theorems.
-/

open scoped BigOperators

namespace DkMathTest.GTailSelection

open DkMath.CosmicFormula

variable {R : Type*} [CommSemiring R]

-- Canonical degree-three cut, including its selected interpretation.
example (x u : R) :
    selectedBody 3 (Finset.Ico 2 4) x u = x ^ 2 * (x + 3 * u) := by
  rw [selectedBody_Ico 3 2 x u (by decide)]
  simp [GTail, Finset.sum_range_succ]
  ring

example (x u : R) :
    (x + u) ^ 3 = (u ^ 3 + 3 * x * u ^ 2) + x ^ 2 * (x + 3 * u) := by
  calc
    (x + u) ^ 3 = (∑ j ∈ Finset.range 2, (Nat.choose 3 j : R) * x ^ j * u ^ (3 - j))
        + x ^ 2 * GTail 3 2 x u := add_pow_eq_prefix_add_xpow_mul_GTail 3 2 x u (by decide)
    _ = _ := by
      simp [GTail, Finset.sum_range_succ]
      ring

-- Exactly the six interior terms, without downstream factorization.
example (x u : R) :
    selectedBody 7 {1, 2, 3, 4, 5, 6} x u =
      7 * x * u ^ 6 + 21 * x ^ 2 * u ^ 5 + 35 * x ^ 3 * u ^ 4
        + 35 * x ^ 4 * u ^ 3 + 21 * x ^ 5 * u ^ 2 + 7 * x ^ 6 * u := by
  norm_num [selectedBody, selectedTerm, Finset.sum_range_succ, Finset.sum_filter, Nat.choose]

example (x u : R) :
    selectedGap 7 {1, 2, 3, 4, 5, 6} x u = u ^ 7 + x ^ 7 := by
  norm_num [selectedGap, selectedTerm, Finset.sum_range_succ, Finset.sum_filter, Nat.choose]

example (x u : R) :
    selectedBody 0 ∅ x u = 0 ∧ selectedGap 0 ∅ x u = 1 ∧
    selectedBody 0 (Finset.range 1) x u = 1 ∧ selectedGap 0 (Finset.range 1) x u = 0 := by
  constructor
  · exact selectedBody_empty 0 x u
  constructor
  · simpa only [pow_zero] using selectedGap_empty 0 x u
  constructor
  · simpa only [Nat.zero_add, pow_zero] using selectedBody_full 0 x u
  · exact selectedGap_full 0 x u

example (d : ℕ) (x u : R) :
    selectedBody d (Finset.Ico 0 (d + 1)) x u = (x + u) ^ d := by
  rw [selectedBody_Ico d 0 x u (Nat.zero_le d), pow_zero, one_mul, GTail_zero_eq_add_pow]

example (d : ℕ) (x u : R) :
    selectedBody d (Finset.Ico d (d + 1)) x u = x ^ d := by
  rw [selectedBody_Ico d d x u le_rfl, GTail_self_eq_one, mul_one]

example (d r : ℕ) (u : R) (hr : r ≤ d) :
    selectedBody d (Finset.Ico r (d + 1)) 0 u = (0 : R) ^ r * GTail d r 0 u :=
  selectedBody_Ico d r 0 u hr

example (d r : ℕ) (x : R) (hr : r ≤ d) :
    selectedBody d (Finset.Ico r (d + 1)) x 0 = x ^ r * GTail d r x 0 :=
  selectedBody_Ico d r x 0 hr

example (x u : R) : selectedBody 0 {42} x u = 0 := by
  simp [selectedBody]

end DkMathTest.GTailSelection

#print axioms DkMath.CosmicFormula.selectedGap_add_selectedBody
#print axioms DkMath.CosmicFormula.selectedBody_empty
#print axioms DkMath.CosmicFormula.selectedGap_empty
#print axioms DkMath.CosmicFormula.selectedBody_full
#print axioms DkMath.CosmicFormula.selectedGap_full
#print axioms DkMath.CosmicFormula.selectedBody_complement
#print axioms DkMath.CosmicFormula.selectedGap_complement
#print axioms DkMath.CosmicFormula.selectedBody_singleton
#print axioms DkMath.CosmicFormula.selectedBody_Ico
#print axioms DkMath.CosmicFormula.selectedGap_Ico
