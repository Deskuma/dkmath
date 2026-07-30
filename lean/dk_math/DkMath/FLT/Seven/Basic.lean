/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.FLT.Seven.Basic"

namespace DkMath.FLT.Seven

/-- The exponent-seven Fermat equation over natural numbers. -/
def Fermat7Equation (x y z : ℕ) : Prop :=
  x ^ 7 + y ^ 7 = z ^ 7

/-- A positive primitive exponent-seven candidate. -/
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat7Equation x y z

theorem seventh_sub_eq_of_add_eq {x y z : ℕ} (hEq : Fermat7Equation x y z) :
    z ^ 7 - y ^ 7 = x ^ 7 := by
  unfold Fermat7Equation at hEq
  omega

theorem right_lt_of_fermat7Equation {x y z : ℕ}
    (hx : 0 < x) (hEq : Fermat7Equation x y z) : y < z := by
  unfold Fermat7Equation at hEq
  have hx7 : 0 < x ^ 7 := pow_pos hx 7
  have hyz : y ^ 7 < z ^ 7 := by omega
  exact (Nat.pow_lt_pow_iff_left (by decide : 7 ≠ 0)).mp hyz

theorem gap_pos_of_fermat7Equation {x y z : ℕ}
    (hx : 0 < x) (hEq : Fermat7Equation x y z) : 0 < z - y :=
  Nat.sub_pos_of_lt (right_lt_of_fermat7Equation hx hEq)

end DkMath.FLT.Seven
