/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.NumberTheory.PrimitiveSet.RealWeight"

namespace DkMath.NumberTheory.PrimitiveSet

/--
A finite toy base-prime weight with real values is nonnegative everywhere.

This is the first R-version analogue of `BasePrimeToyWeight`.  It intentionally
does not mention `Real.log`; logarithmic candidates are added only after the
real ratio skeleton is stable.
-/
def RealBasePrimeToyWeight (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ n p, 0 ≤ c n p

/-- A real ratio-style finite toy base-prime weight `c n p = A p / B n`. -/
noncomputable def realRatioBasePrimeWeight (A B : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n p => A p / B n

/--
A real ratio-style base-prime weight is globally nonnegative when the numerator
is nonnegative and the denominator is positive.
-/
theorem realRatioBasePrimeWeight_realBasePrimeToyWeight
    (A B : ℕ → ℝ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n) :
    RealBasePrimeToyWeight (realRatioBasePrimeWeight A B) := by
  intro n p
  exact div_nonneg (hA p) (le_of_lt (hB n))

end DkMath.NumberTheory.PrimitiveSet
