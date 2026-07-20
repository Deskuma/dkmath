/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.FLT.Five.Basic"

namespace DkMath.FLT.Five

/-- The exponent-five Fermat equation. -/
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5

/-- Positive coprime data for a candidate exponent-five counterexample. -/
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z

/-- Rewrite a Fermat-five equation as a difference of fifth powers. -/
theorem fifth_sub_eq_of_add_eq
    {x y z : ℕ}
    (hEq : Fermat5Equation x y z) :
    z ^ 5 - y ^ 5 = x ^ 5 := by
  unfold Fermat5Equation at hEq
  omega

/-- A positive left term forces the right base above the second base. -/
theorem right_lt_of_fermat5Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    y < z := by
  unfold Fermat5Equation at hEq
  have hx5 : 0 < x ^ 5 := pow_pos hx 5
  have hy5z5 : y ^ 5 < z ^ 5 := by
    omega
  exact (Nat.pow_lt_pow_iff_left (by decide : 5 ≠ 0)).mp hy5z5

/-- The gap `z-y` is positive for a positive Fermat-five left term. -/
theorem gap_pos_of_fermat5Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    0 < z - y := by
  exact Nat.sub_pos_of_lt (right_lt_of_fermat5Equation hx hEq)

end DkMath.FLT.Five
