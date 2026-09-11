/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Basic

#print "file: DkMath.NumberTheory.QuadraticConjugateFactor"

namespace DkMath.NumberTheory.QuadraticConjugateFactor

/-! ## The raw conjugate-factor identity -/

/-- The difference of two conjugate factors has the expected discriminant. -/
theorem add_sq_sub_four_mul_eq_sub_sq {R : Type*} [CommRing R] (U V : R) :
    (U + V) ^ 2 - 4 * (U * V) = (U - V) ^ 2 := by
  ring

/-! ## The division-free Gauss-form rearrangement -/

/--
If `R` is the sum of two conjugate factors, `C` their product, and their
difference has square `D * S^2`, then the product satisfies the corresponding
Gauss form.  The statement is deliberately independent of cyclotomic fields.
-/
theorem four_mul_product_eq_sum_sq_sub_discriminant_mul
    {α : Type*} [CommRing α]
    {R U V C T D S : α}
    (hR : R = U + V)
    (hC : C = U * V)
    (hDiff : (U - V) ^ 2 = D * S ^ 2)
    (hD : T = D) :
    4 * C = R ^ 2 - T * S ^ 2 := by
  calc
    4 * C = 4 * (U * V) := by rw [hC]
    _ = (U + V) ^ 2 - (U - V) ^ 2 := by ring
    _ = R ^ 2 - D * S ^ 2 := by rw [hR, hDiff]
    _ = R ^ 2 - T * S ^ 2 := by rw [hD]

end DkMath.NumberTheory.QuadraticConjugateFactor
