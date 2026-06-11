/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.GNBridge
import DkMath.NumberTheory.Gcd.GN

#print "file: DkMath.Petal.GcdBridge"

/-!
# Petal GCD Bridge

This file exposes the existing `GN` gcd theorems on the Petal `S0_nat`
surface.

The main translation is the degree-three identity
`S0_nat c b = GN 3 (c - b) b`.
-/

namespace DkMath
namespace Petal

open DkMath.FLT.PetalDetect

/--
If `c` and `b` are coprime, then the Petal boundary gap `c - b` is coprime to
`b`.

This is the standard subtraction form of coprimality used to enter the GN gcd
API from Petal coordinates.
-/
theorem coprime_sub_right_of_coprime
    {c b : ℕ} (hbc : b ≤ c) (hcop : Nat.Coprime c b) :
    Nat.Coprime (c - b) b := by
  exact (Nat.coprime_sub_self_left hbc).2 hcop

/--
Degree-three Petal gcd formula.

In coprime Petal coordinates, the common divisor between the boundary gap and
the `S0_nat` detector is exactly the common divisor between the gap and `3`.
-/
theorem gcd_sub_S0_nat_eq_gcd_sub_three
    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b) :
    Nat.gcd (c - b) (S0_nat c b) = Nat.gcd (c - b) 3 := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    DkMath.NumberTheory.Gcd.gcd_boundary_GN_three_eq_gcd_boundary_three
      (x := c - b) (u := b)
      (coprime_sub_right_of_coprime hbc.le hcop)

/--
The degree-three Petal boundary/S0 gcd always divides `3` in coprime Petal
coordinates.
-/
theorem gcd_sub_S0_nat_dvd_three
    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b) :
    Nat.gcd (c - b) (S0_nat c b) ∣ 3 := by
  rw [gcd_sub_S0_nat_eq_gcd_sub_three hbc hcop]
  exact Nat.gcd_dvd_right (c - b) 3

/--
If `c` and `b` are coprime and `3` does not divide the boundary gap, then the
gap is coprime to the Petal detector `S0_nat`.
-/
theorem coprime_sub_S0_nat_of_coprime_of_not_dvd_three
    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b)
    (h3 : ¬ 3 ∣ c - b) :
    Nat.Coprime (c - b) (S0_nat c b) := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    DkMath.NumberTheory.Gcd.coprime_boundary_GN_three_of_coprime_of_not_dvd_three
      (x := c - b) (u := b)
      (coprime_sub_right_of_coprime hbc.le hcop) h3

end Petal
end DkMath
