/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.GcdBridge

#print "file: DkMath.Petal.PadicBridge"

/-!
# Petal p-adic Bridge

This file exposes existing `GN` p-adic valuation theorems on the degree-three
Petal `S0_nat` surface.
-/

namespace DkMath
namespace Petal

open DkMath.FLT.PetalDetect

/--
If a prime `q` does not divide the boundary gap, then the `q`-adic valuation of
the cubic difference is exactly the `q`-adic valuation of the Petal detector
`S0_nat`.
-/
theorem padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
    (hq : Nat.Prime q) (hq_not_dvd_sub : ¬ q ∣ c - b) :
    padicValNat q (c ^ 3 - b ^ 3) = padicValNat q (S0_nat c b) := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
      (p := 3) (z := c) (y := b) (q := q)
      (by norm_num : 2 ≤ 3) hbc hb hq hq_not_dvd_sub

/--
Special case for the boundary prime `3`.

When `3` does not divide the gap, the `3`-adic height of `c^3 - b^3` is read
directly from `S0_nat`.
-/
theorem padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b) (h3 : ¬ 3 ∣ c - b) :
    padicValNat 3 (c ^ 3 - b ^ 3) = padicValNat 3 (S0_nat c b) := by
  exact
    padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
      hbc hb Nat.prime_three h3

end Petal
end DkMath
