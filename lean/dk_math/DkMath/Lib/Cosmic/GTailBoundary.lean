/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail

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

end DkMath.CosmicFormula
