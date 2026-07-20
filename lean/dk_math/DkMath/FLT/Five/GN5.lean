/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.Basic

#print "file: DkMath.FLT.Five.GN5"

namespace DkMath.FLT.Five

/-- The exponent-five GN polynomial in gap/body coordinates. -/
def GN5 (g y : ℕ) : ℕ :=
  g ^ 4
    + 5 * g ^ 3 * y
    + 10 * g ^ 2 * y ^ 2
    + 10 * g * y ^ 3
    + 5 * y ^ 4

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
