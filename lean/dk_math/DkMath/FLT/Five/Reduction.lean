/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GN5

#print "file: DkMath.FLT.Five.Reduction"

namespace DkMath.FLT.Five

/-!
# Primitive factor separation away from five

For a primitive candidate the gap `g=z-y` is coprime to `y`.  The congruence
`GN5(g,y) ≡ 5*y^4 (mod g)` then shows that any common prime of `g` and `GN5(g,y)`
is five.  In Branch B, where `5` does not divide the gap, the two factors are coprime
and their fifth-power product splits into two fifth powers.
-/

/-- A counterexample pack forces the second and result coordinates to be coprime. -/
theorem coprime_y_z_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime y z := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd y z) hg with
    ⟨q, hq, hqgcd⟩
  have hqy : q ∣ y := hqgcd.trans (Nat.gcd_dvd_left y z)
  have hqz : q ∣ z := hqgcd.trans (Nat.gcd_dvd_right y z)
  have hqyp : q ∣ y ^ 5 := hqy.trans (dvd_pow_self y (by decide))
  have hqzp : q ∣ z ^ 5 := hqz.trans (dvd_pow_self z (by decide))
  have hqxp : q ∣ x ^ 5 := by
    have hqsum : q ∣ x ^ 5 + y ^ 5 := by
      rw [hPack.hEq]
      exact hqzp
    exact (Nat.dvd_add_left hqyp).mp hqsum
  have hqx : q ∣ x := hq.dvd_of_dvd_pow hqxp
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqx hqy) hPack.hxy

/-- The natural gap and the second coordinate are coprime. -/
theorem coprime_gap_y_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime (z - y) y := by
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hyGap : Nat.Coprime y (z - y) :=
    (Nat.coprime_sub_self_right hyz).2
      (coprime_y_z_of_counterexamplePack hPack)
  simpa [Nat.coprime_comm] using hyGap

/-- Modulo the gap, `GN5 g y` reduces to its exceptional term `5*y^4`. -/
theorem dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
    {g y q : ℕ} (hqg : q ∣ g) (hqGN : q ∣ GN5 g y) :
    q ∣ 5 * y ^ 4 := by
  have hdecomp :
      GN5 g y =
        g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) +
          5 * y ^ 4 := by
    exact GN5_eq_gap_mul_add_five_mul_y_pow_four g y
  have hqPrefix :
      q ∣ g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) :=
    dvd_mul_of_dvd_left hqg _
  rw [hdecomp] at hqGN
  exact (Nat.dvd_add_right hqPrefix).mp hqGN

/-- Away from the exceptional prime five, the gap and `GN5` are coprime. -/
theorem coprime_gap_GN5_of_coprime_of_five_not_dvd
    {g y : ℕ} (hgy : Nat.Coprime g y) (h5g : ¬ 5 ∣ g) :
    Nat.Coprime g (GN5 g y) := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd g (GN5 g y)) hg with
    ⟨q, hq, hqgcd⟩
  have hqg : q ∣ g := hqgcd.trans (Nat.gcd_dvd_left g (GN5 g y))
  have hqGN : q ∣ GN5 g y :=
    hqgcd.trans (Nat.gcd_dvd_right g (GN5 g y))
  have hq5y : q ∣ 5 * y ^ 4 :=
    dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5 hqg hqGN
  rcases hq.dvd_mul.mp hq5y with hq5 | hqy4
  · have hqeq : q = 5 :=
      ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hq5).resolve_left hq.ne_one
    exact h5g (hqeq ▸ hqg)
  · have hqy : q ∣ y := hq.dvd_of_dvd_pow hqy4
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqg hqy) hgy

/-- The Branch-B hypothesis removes the only exceptional common factor. -/
theorem branchB_coprime_gap_GN5
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    Nat.Coprime (z - y) (GN5 (z - y) y) :=
  coprime_gap_GN5_of_coprime_of_five_not_dvd
    (coprime_gap_y_of_counterexamplePack hPack) hBranch

/-- Coprime factors whose product is a fifth power are individually fifth powers. -/
theorem fifth_power_factor_split
    {g n x : ℕ} (hcop : Nat.Coprime g n) (hbody : g * n = x ^ 5) :
    (∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5) := by
  have hunit : IsUnit (GCDMonoid.gcd g n) := by
    simpa [Nat.Coprime] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd n g) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)

/-- Exact elementary normal form forced by a Branch-B counterexample. -/
theorem branchB_fifth_power_factor_split
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    (∃ a : ℕ, z - y = a ^ 5) ∧
      (∃ b : ℕ, GN5 (z - y) y = b ^ 5) := by
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
    rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
    exact fifth_sub_eq_of_add_eq hPack.hEq
  exact fifth_power_factor_split (branchB_coprime_gap_GN5 hPack hBranch) hbody

/-- A GN5-not-fifth-power theorem would close Branch B directly. -/
theorem branchB_false_of_GN5_not_fifth_power
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y)
    (hGN : ¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5) :
    False := by
  exact hGN (branchB_fifth_power_factor_split hPack hBranch).2

end DkMath.FLT.Five
