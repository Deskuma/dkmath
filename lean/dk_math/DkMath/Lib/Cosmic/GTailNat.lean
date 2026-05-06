/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail

#print "file: DkMath.Lib.Cosmic.GTailNat"

/-!
## Natural-number divisibility layer for `GTail`

This file contains the `ℕ`-specific divisibility consequences of the general
tail decomposition.
-/

open scoped BigOperators

namespace DkMath.CosmicFormula

/--
On `ℕ`, the higher tail is divisible by its boundary power `x^r`.

This is the natural divisibility corollary of the higher-tail factorization and
serves as the lower-bound half of future valuation theorems.
-/
theorem pow_dvd_higher_tail
    (d r x u : ℕ) (hr : r ≤ d) :
    x ^ r ∣
      ((x + u) ^ d -
        ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) := by
  refine ⟨GTail d r x u, ?_⟩
  calc
    (x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)
      = ((∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) +
          x ^ r * GTail d r x u) -
        ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j) := by
          simpa using
            congrArg
              (fun t =>
                t - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j))
              (add_pow_eq_prefix_add_xpow_mul_GTail (R := ℕ) d r x u hr)
    _ = x ^ r * GTail d r x u := by
          exact Nat.add_sub_cancel_left _ _

/--
If the leading term of `GTail_rec` is a `p`-adic unit and `p ∣ x`, then `p`
does not divide the normalized higher tail.
-/
theorem GTail_not_dvd_of_head_unit_of_prime_dvd_x
    {p d r x u : ℕ}
    (_hp : Nat.Prime p) (hr : r < d)
    (hhead : ¬ p ∣ Nat.choose d r * u ^ (d - r))
    (hpx : p ∣ x) :
    ¬ p ∣ GTail d r x u := by
  intro htail
  rw [GTail_rec (R := ℕ) d r x u hr] at htail
  have hmul : p ∣ x * GTail d (r + 1) x u := dvd_mul_of_dvd_left hpx _
  have hhead_dvd : p ∣ Nat.choose d r * u ^ (d - r) :=
    (Nat.dvd_add_right hmul).1 (by simpa [Nat.add_comm] using htail)
  exact hhead hhead_dvd

/--
`r = 1` specialization of `GTail_not_dvd_of_head_unit_of_prime_dvd_x`.

[GNZC] This is the non-divisibility kernel for the standard `GN` layer.
-/
theorem GN_not_dvd_of_head_unit_of_prime_dvd_x
    {p d x u : ℕ}
    (hp : Nat.Prime p) (hd : 1 < d)
    (hhead : ¬ p ∣ Nat.choose d 1 * u ^ (d - 1))
    (hpx : p ∣ x) :
    ¬ p ∣ GTail d 1 x u :=
  GTail_not_dvd_of_head_unit_of_prime_dvd_x hp hd hhead hpx

end DkMath.CosmicFormula
