/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail

#print "file: DkMath.Lib.Cosmic.GTailBoundary"

/-!
# Boundary gcd for `GTail`

This module records the exact natural-number gcd carried by the first term of
the `GTail` recursion.  The result is stated for the general depth `r`; the
usual `GN` boundary formula is only a specialization.

The statements here are finite divisibility identities.  They do not assert a
prime-exponent theorem or perform any downstream migration.
-/

namespace DkMath.CosmicFormula

/--
The gcd of `x` with a `GTail` is exactly the gcd with its boundary head.

The endpoint `r = d` is handled by `GTail d d x u = 1`; otherwise
`GTail_rec` expresses the tail as the boundary head plus a multiple of `x`.
-/
theorem gcd_GTail_eq_gcd_boundary
    (d r x u : ℕ) (hr : r ≤ d) :
    Nat.gcd x (GTail d r x u) =
      Nat.gcd x (Nat.choose d r * u ^ (d - r)) := by
  by_cases hrd : r = d
  · subst r
    simp
  · have hlt : r < d := lt_of_le_of_ne hr hrd
    rw [GTail_rec d r x u hlt]
    rw [Nat.gcd_add_mul_left_right]
    simp

/--
Under `Coprime x u`, the boundary gcd is carried solely by the Pascal
coefficient `choose d r`.
-/
theorem gcd_GTail_eq_gcd_choose
    (d r x u : ℕ) (hr : r ≤ d) (hcop : Nat.Coprime x u) :
    Nat.gcd x (GTail d r x u) = Nat.gcd x (Nat.choose d r) := by
  rw [gcd_GTail_eq_gcd_boundary d r x u hr]
  have hpow : Nat.Coprime x (u ^ (d - r)) :=
    Nat.Coprime.pow_right (d - r) hcop
  rw [Nat.gcd_comm, hpow.symm.gcd_mul_right_cancel, Nat.gcd_comm]

/--
The `r = 1` boundary gcd in the canonical `GN` vocabulary.

The only range assumption is `1 ≤ d`; primality is not needed for this
identity.
-/
theorem gcd_GN_eq_gcd_of_one_le
    {d g u : ℕ} (hd : 1 ≤ d) (hcop : Nat.Coprime g u) :
    Nat.gcd g (GTail d 1 g u) = Nat.gcd g d := by
  exact gcd_GTail_eq_gcd_choose d 1 g u hd hcop |>.trans (by
    simp [Nat.choose_one_right])

/-- The off-prime branch of the prime `GN` boundary gcd. -/
theorem gcd_GN_prime_eq_one_of_not_dvd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u)
    (hpg : ¬ p ∣ g) :
    Nat.gcd g (GTail p 1 g u) = 1 := by
  rw [gcd_GN_eq_gcd_of_one_le hp.one_le hcop]
  have hgcd : Nat.gcd g p ∣ p := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime hp).mp hgcd with h | h
  · exact h
  · exfalso
    apply hpg
    rw [← h]
    exact Nat.gcd_dvd_left _ _

/-- The ramified branch of the prime `GN` boundary gcd. -/
theorem gcd_GN_prime_eq_prime_of_dvd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    Nat.gcd g (GTail p 1 g u) = p := by
  rw [gcd_GN_eq_gcd_of_one_le hp.one_le hcop]
  apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
  apply Nat.dvd_gcd hpg
  exact Nat.dvd_refl p

end DkMath.CosmicFormula
