 /-
 Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
 Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/

import DkMath.Lib.Cosmic.GTailCongruence
import DkMath.ABC.PadicValNat

#print "file: DkMath.CosmicFormula.GTail"

open scoped BigOperators

namespace DkMath.CosmicFormula

/--
Under the head-unit condition, the normalized higher tail has `p`-adic
valuation zero.
-/
theorem padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
    {p d r x u : ℕ}
    (hp : Nat.Prime p) (hr : r < d)
    (hhead : ¬ p ∣ Nat.choose d r * u ^ (d - r))
    (hpx : p ∣ x) :
    padicValNat p (GTail d r x u) = 0 := by
  exact padicValNat.eq_zero_of_not_dvd
    (GTail_not_dvd_of_head_unit_of_prime_dvd_x hp hr hhead hpx)

/--
`r = 1` specialization of the normalized-tail valuation-zero theorem.
-/
theorem padicValNat_GN_eq_zero_of_head_unit_of_prime_dvd_x
    {p d x u : ℕ}
    (hp : Nat.Prime p) (hd : 1 < d)
    (hhead : ¬ p ∣ Nat.choose d 1 * u ^ (d - 1))
    (hpx : p ∣ x) :
    padicValNat p (GTail d 1 x u) = 0 :=
  padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x hp hd hhead hpx

/--
Lower-bound half of the higher-tail valuation mechanism.

Since the higher tail carries the boundary factor `x^r`, its `p`-adic
valuation is at least `r * v_p(x)` whenever the tail itself is nonzero.
-/
theorem padicValNat_higher_tail_lower_bound
    {p d r x u : ℕ}
    (hp : Nat.Prime p) (hr : r ≤ d)
    (htail_ne :
      ((x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) ≠ 0) :
    r * padicValNat p x ≤
      padicValNat p
        ((x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) := by
  have hxdvd :=
    pow_dvd_higher_tail d r x u hr
  have hxpow_ne : x ^ r ≠ 0 := by
    intro hxpow0
    rcases hxdvd with ⟨k, hk⟩
    apply htail_ne
    rw [hk, hxpow0, zero_mul]
  have hvxpow : padicValNat p (x ^ r) = r * padicValNat p x :=
    DkMath.ABC.padicValNat_pow' hp r hxpow_ne
  have hpk_dvd_xpow : p ^ (r * padicValNat p x) ∣ x ^ r := by
    exact (DkMath.ABC.padicValNat_le_iff_dvd hp hxpow_ne (r * padicValNat p x)).mp
      (by simp [hvxpow])
  have hpk_dvd_tail :
      p ^ (r * padicValNat p x) ∣
        ((x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) :=
    dvd_trans hpk_dvd_xpow hxdvd
  exact (DkMath.ABC.padicValNat_le_iff_dvd hp htail_ne (r * padicValNat p x)).mpr
    hpk_dvd_tail

/--
Exact higher-tail valuation when the head term is a `p`-adic unit.

The normalized tail has valuation zero, so the full higher tail inherits
exactly the boundary contribution `r * v_p(x)`.
-/
theorem padicValNat_tail_exact_of_head_unit
    {p d r x u : ℕ}
    (hp : Nat.Prime p) (hr : r < d)
    (htail_ne :
      ((x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) ≠ 0)
    (hhead : ¬ p ∣ Nat.choose d r * u ^ (d - r))
    (hpx : p ∣ x) :
    padicValNat p
      ((x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j))
      = r * padicValNat p x := by
  have hrle : r ≤ d := Nat.le_of_lt hr
  have hfactor :
      ((x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j))
        = x ^ r * GTail d r x u := by
    calc
      (x + u) ^ d - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)
        = ((∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j)) +
            x ^ r * GTail d r x u) -
          ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j) := by
            simpa using
              congrArg
                (fun t =>
                  t - ∑ j ∈ Finset.range r, Nat.choose d j * x ^ j * u ^ (d - j))
                (add_pow_eq_prefix_add_xpow_mul_GTail (R := ℕ) d r x u hrle)
      _ = x ^ r * GTail d r x u := by
            exact Nat.add_sub_cancel_left _ _
  have hgtail_not :
      ¬ p ∣ GTail d r x u :=
    GTail_not_dvd_of_head_unit_of_prime_dvd_x hp hr hhead hpx
  have hgtail_ne : GTail d r x u ≠ 0 := by
    intro h0
    exact hgtail_not (by rw [h0]; exact dvd_zero p)
  have hxpow_ne : x ^ r ≠ 0 := by
    intro hxpow0
    apply htail_ne
    rw [hfactor, hxpow0, zero_mul]
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [hfactor]
  rw [padicValNat.mul hxpow_ne hgtail_ne]
  rw [DkMath.ABC.padicValNat_pow' hp r hxpow_ne]
  rw [padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x hp hr hhead hpx]
  simp

/--
`r = 1` specialization of the exact higher-tail valuation theorem.

[GNZC] This is the exact valuation theorem for the standard `GN` layer.
-/
theorem padicValNat_GN_exact_of_head_unit
    {p d x u : ℕ}
    (hp : Nat.Prime p) (hd : 1 < d)
    (hGN_ne : ((x + u) ^ d - u ^ d) ≠ 0)
    (hhead : ¬ p ∣ Nat.choose d 1 * u ^ (d - 1))
    (hpx : p ∣ x) :
    padicValNat p ((x + u) ^ d - u ^ d) = padicValNat p x := by
  simpa using
    (padicValNat_tail_exact_of_head_unit
      (p := p) (d := d) (r := 1) (x := x) (u := u)
      hp hd
      (by
        simpa [Finset.range_one, Nat.choose_zero_right, Nat.cast_one,
          pow_zero, one_mul] using hGN_ne)
      hhead hpx)

end DkMath.CosmicFormula
