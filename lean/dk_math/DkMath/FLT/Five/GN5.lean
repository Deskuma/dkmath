/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.Basic

#print "file: DkMath.FLT.Five.GN5"

namespace DkMath.FLT.Five

/-!
# The homogeneous fifth cyclotomic factor in gap coordinates

Write `z = g + y`.  The polynomial `GN5 g y` is the usual quotient

`(z^5 - y^5) / (z - y) = z^4 + z^3*y + z^2*y^2 + z*y^3 + y^4`

after substituting `z = g + y`.  Thus `(g+y)^5-y^5 = g * GN5 g y`.  The two
decomposition theorems below expose its reductions modulo the gap and modulo five;
these explain why five is the only exceptional common prime in the primitive route.
-/

/-- The homogeneous fifth cyclotomic quotient expressed in the local coordinates
`z = g + y`. -/
def GN5 (g y : ℕ) : ℕ :=
  g ^ 4
    + 5 * g ^ 3 * y
    + 10 * g ^ 2 * y ^ 2
    + 10 * g * y ^ 3
    + 5 * y ^ 4

/-- Identification of `GN5` with the standard homogeneous fifth cyclotomic factor. -/
theorem GN5_eq_homogeneous_cyclotomic (g y : ℕ) :
    GN5 g y =
      (g + y) ^ 4 + (g + y) ^ 3 * y + (g + y) ^ 2 * y ^ 2 +
        (g + y) * y ^ 3 + y ^ 4 := by
  unfold GN5
  ring

/-- Gap decomposition: `GN5(g,y) ≡ 5*y^4 (mod g)`. -/
theorem GN5_eq_gap_mul_add_five_mul_y_pow_four (g y : ℕ) :
    GN5 g y =
      g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) +
        5 * y ^ 4 := by
  unfold GN5
  ring

/-- Five-adic decomposition: `GN5(g,y) ≡ g^4 (mod 5)`. -/
theorem GN5_eq_g_pow_four_add_five_mul (g y : ℕ) :
    GN5 g y =
      g ^ 4 + 5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 +
        2 * g * y ^ 3 + y ^ 4) := by
  unfold GN5
  ring

/-- The fifth-power body decomposition before subtraction. -/
theorem add_pow_five_eq_add_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 = y ^ 5 + g * GN5 g y := by
  unfold GN5
  ring

/-- The fifth-power body is the gap multiplied by `GN5`. -/
theorem add_pow_five_sub_eq_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 - y ^ 5 = g * GN5 g y := by
  rw [add_pow_five_eq_add_mul_GN5]
  omega

/-- Difference-of-fifth-powers form using the natural-number gap. -/
theorem pow_five_sub_pow_five_eq_gap_mul_GN5
    {y z : ℕ}
    (hyz : y ≤ z) :
    z ^ 5 - y ^ 5 = (z - y) * GN5 (z - y) y := by
  simpa [Nat.sub_add_cancel hyz] using
    (add_pow_five_sub_eq_mul_GN5 (z - y) y)

/-- The concrete GN5 value used by the finite-prime escape demonstration. -/
theorem GN5_one_one : GN5 1 1 = 31 := by
  norm_num [GN5]

/-- A second small evaluation for smoke testing. -/
theorem GN5_two_one : GN5 2 1 = 121 := by
  norm_num [GN5]

end DkMath.FLT.Five
