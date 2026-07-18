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

/-- Coprime left inputs force the second input and the result to be coprime. -/
theorem coprime_right_of_fermat5Equation
    {x y z : ℕ}
    (hxy : Nat.Coprime x y)
    (hEq : Fermat5Equation x y z) :
    Nat.Coprime y z := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg1
  have hg_ne1 : Nat.gcd y z ≠ 1 := by
    simpa using hg1
  rcases Nat.exists_prime_and_dvd hg_ne1 with ⟨q, hqPrime, hq_dvd_g⟩
  have hq_dvd_y : q ∣ y :=
    dvd_trans hq_dvd_g (Nat.gcd_dvd_left y z)
  have hq_dvd_z : q ∣ z :=
    dvd_trans hq_dvd_g (Nat.gcd_dvd_right y z)
  have hq_dvd_y5 : q ∣ y ^ 5 :=
    dvd_trans hq_dvd_y (dvd_pow_self y (by decide : 5 ≠ 0))
  have hq_dvd_z5 : q ∣ z ^ 5 :=
    dvd_trans hq_dvd_z (dvd_pow_self z (by decide : 5 ≠ 0))
  have hq_dvd_sum : q ∣ x ^ 5 + y ^ 5 := by
    rw [hEq]
    exact hq_dvd_z5
  have hq_dvd_x5 : q ∣ x ^ 5 := by
    exact (Nat.dvd_add_left hq_dvd_y5).1 hq_dvd_sum
  have hq_dvd_x : q ∣ x := hqPrime.dvd_of_dvd_pow hq_dvd_x5
  have hnot : ¬ Nat.Coprime x y :=
    Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hq_dvd_x hq_dvd_y
  exact hnot hxy

namespace CounterexamplePack

/-- A candidate counterexample has coprime right input and result. -/
theorem coprime_right
    {x y z : ℕ}
    (h : CounterexamplePack x y z) :
    Nat.Coprime y z := by
  exact coprime_right_of_fermat5Equation h.hxy h.hEq

/-- The local gap `z-y` is coprime to the right input. -/
theorem gap_coprime_right
    {x y z : ℕ}
    (h : CounterexamplePack x y z) :
    Nat.Coprime (z - y) y := by
  have hyz : y ≤ z :=
    Nat.le_of_lt (right_lt_of_fermat5Equation h.hx h.hEq)
  have hySub : Nat.Coprime y (z - y) :=
    (Nat.coprime_sub_self_right hyz).2 h.coprime_right
  simpa [Nat.coprime_comm] using hySub

end CounterexamplePack

end DkMath.FLT.Five
