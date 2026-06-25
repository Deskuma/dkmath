/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.PadicBridge
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.FLT.PhaseLift

#print "file: DkMath.Petal.PrimitiveBridge"

/-!
# Petal Primitive Bridge

This file connects the Petal `S0_nat` detector to the existing primitive-prime
factor API.

It intentionally stays thin: primitive-prime existence and no-lift machinery
remain in the established `NumberTheory` and `FLT` files, while this file gives
Petal-facing names for the degree-three entry points.
-/

namespace DkMath
namespace Petal

open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.PrimitiveBeam

/--
A primitive prime factor of `c^3 - b^3` divides the Petal detector `S0_nat`.
-/
theorem primitive_prime_dvd_S0_nat
    {q c b : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q c b 3)
    (hbc : b < c) :
    q ∣ S0_nat c b := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    primitive_prime_dvd_GN
      (q := q) (a := c) (b := b) (d := 3)
      hq (by norm_num : 0 < 3) (by norm_num : 1 < 3) hbc

/--
A primitive prime factor of `c^3 - b^3` has the same `q`-adic height on the
cubic difference and on the Petal detector `S0_nat`.
-/
theorem primitive_prime_padicValNat_cube_sub_eq_S0_nat
    {q c b : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q c b 3)
    (hbc : b < c) :
    padicValNat q (c ^ 3 - b ^ 3) = padicValNat q (S0_nat c b) := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    primitive_prime_padic_eq_GN
      (q := q) (a := c) (b := b) (d := 3)
      hq (by norm_num : 0 < 3) (by norm_num : 1 < 3) hbc

/--
Petal-facing constructor for the existing `PrimitiveOnS0` predicate.

Any prime divisor of the cubic difference that avoids the boundary gap becomes
a primitive-on-`S0` witness after passing through the Cosmic/Petal bridge.
-/
theorem primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
    {c b q : ℕ} (hbc : b < c)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
    (hq_not_dvd_sub : ¬ q ∣ c - b) :
    DkMath.FLT.PrimitiveOnS0 c b q := by
  exact
    ⟨hq,
      DkMath.FLT.prime_dvd_S0_via_cosmic_bridge hbc hq hq_dvd hq_not_dvd_sub,
      hq_not_dvd_sub⟩

/--
Zsigmondy degree-three existence, returned directly as a `PrimitiveOnS0`
witness in Petal coordinates.
-/
theorem exists_primitiveOnS0_of_not_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, DkMath.FLT.PrimitiveOnS0 c b q := by
  rcases DkMath.FLT.exists_prime_factor_cube_diff_of_not_three_dvd_sub
      hbc hb hcop h3 with ⟨q, hq, hq_dvd, hq_not_dvd_sub⟩
  exact ⟨q, primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub hbc hq hq_dvd hq_not_dvd_sub⟩

/--
Petal-facing projection of the primitive witness.

If the boundary gap is not divisible by `3`, then `S0_nat` has a prime divisor
that does not divide the boundary gap.
-/
theorem exists_prime_dvd_S0_nat_of_not_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b := by
  rcases exists_primitiveOnS0_of_not_three_dvd_sub hbc hb hcop h3 with ⟨q, hprim⟩
  exact ⟨q, hprim.1, hprim.2.1, hprim.2.2⟩

end Petal
end DkMath
