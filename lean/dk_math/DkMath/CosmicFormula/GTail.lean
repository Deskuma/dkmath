 /-
 Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
 Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/

import Mathlib
import DkMath.ABC.PadicValNat

#print "file: DkMath.CosmicFormula.GTail"

open scoped BigOperators

namespace DkMath.CosmicFormula

/--
General tail family of the binomial expansion.

`GTail d r x u` is the normalized tail obtained after removing the first `r`
layers from `(x + u)^d`. The intended regime is `0 ≤ r ≤ d`, but the
definition itself is total.
-/
@[simp] def GTail {R : Type _} [CommSemiring R] (d r : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d + 1 - r),
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))

/--
Tail decomposition of the binomial expansion.

The first `r` layers stay as the prefix sum, and the remaining part factors as
`x^r * GTail d r x u`.
-/
theorem add_pow_eq_prefix_add_xpow_mul_GTail
    {R : Type _} [CommSemiring R]
    (d r : ℕ) (x u : R) (hr : r ≤ d) :
    (x + u) ^ d =
      (∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j))
      + x ^ r * GTail d r x u := by
  let f : ℕ → R := fun j => x ^ j * u ^ (d - j) * (Nat.choose d j : R)
  have hsplit :=
    Finset.sum_range_add_sum_Ico f (show r ≤ d + 1 by omega)
  have hprefix :
      ∑ j ∈ Finset.range r, f j =
        ∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, mul_assoc, mul_left_comm, mul_comm]
  have htail_reindex :
      ∑ j ∈ Finset.Ico r (d + 1), f j =
        ∑ k ∈ Finset.range (d + 1 - r), f (r + k) := by
    have hupper : r + (d + 1 - r) = d + 1 := by
      omega
    calc
      ∑ j ∈ Finset.Ico r (d + 1), f j
          = ∑ j ∈ Finset.Ico r (r + (d + 1 - r)), f j := by
              simp [hupper]
      _ = ∑ k ∈ Finset.Ico 0 (d + 1 - r), f (k + r) := by
              symm
              simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                (Finset.sum_Ico_add' f 0 (d + 1 - r) r)
      _ = ∑ k ∈ Finset.range (d + 1 - r), f (r + k) := by
            rw [Nat.Ico_zero_eq_range]
            apply Finset.sum_congr rfl
            intro k hk
            simp [Nat.add_comm]
  have htail_factor :
      ∑ k ∈ Finset.range (d + 1 - r), f (r + k) =
        x ^ r * GTail d r x u := by
    unfold GTail
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [f, pow_add, mul_assoc, mul_left_comm, mul_comm]
  calc
    (x + u) ^ d = ∑ j ∈ Finset.range (d + 1), f j := by
      simp [f, add_pow]
    _ =
      (∑ j ∈ Finset.range r, f j) +
        ∑ j ∈ Finset.Ico r (d + 1), f j := by
      rw [← hsplit]
    _ =
      (∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j)) +
        ∑ k ∈ Finset.range (d + 1 - r), f (r + k) := by
      rw [hprefix, htail_reindex]
    _ =
      (∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j)) +
        x ^ r * GTail d r x u := by
      rw [htail_factor]

/--
Boundary-factor form of the higher tail identity.

This is the subtraction-shaped reading of
`add_pow_eq_prefix_add_xpow_mul_GTail`, matching the intended
"higher tail = boundary power times normalized kernel" API.
-/
theorem higher_tail_eq_pow_mul_GTail
    {R : Type _} [CommRing R]
    (d r : ℕ) (x u : R) (hr : r ≤ d) :
    (x + u) ^ d -
        (∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j))
      = x ^ r * GTail d r x u := by
  rw [sub_eq_iff_eq_add]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_pow_eq_prefix_add_xpow_mul_GTail d r x u hr

/-- The `r = 0` tail is the whole binomial expansion. -/
theorem GTail_zero_eq_add_pow
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) :
    GTail d 0 x u = (x + u) ^ d := by
  have h := add_pow_eq_prefix_add_xpow_mul_GTail d 0 x u (Nat.zero_le d)
  simpa using h.symm

/-- The top tail is the constant `1`. -/
theorem GTail_self_eq_one
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) :
    GTail d d x u = 1 := by
  unfold GTail
  simp

/--
Recursion for the tail family.

Peeling one more layer from the prefix exposes the `r`-th binomial term and the
next tail.
-/
theorem GTail_rec
    {R : Type _} [CommSemiring R]
    (d r : ℕ) (x u : R) (hr : r < d) :
    GTail d r x u =
      (Nat.choose d r : R) * u ^ (d - r) + x * GTail d (r + 1) x u := by
  unfold GTail
  have hlen : d + 1 - r = (d - r) + 1 := by omega
  rw [hlen, Finset.sum_range_succ']
  have hrest :
      ∑ k ∈ Finset.range (d - r),
        (Nat.choose d (r + (k + 1)) : R) * x ^ (k + 1) * u ^ (d - (r + (k + 1))) =
        x * GTail d (r + 1) x u := by
    unfold GTail
    have hlen' : d + 1 - (r + 1) = d - r := by omega
    rw [hlen', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have harr : r + (k + 1) = r + 1 + k := by
      omega
    rw [harr]
    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  rw [hrest]
  simp [add_comm, add_left_comm]

/--
Migration alias for the higher-tail recursion.

The candidate notes used a `Gbinom`-flavored name before `GTail` became the
canonical family. Keep this alias during the naming transition.
-/
theorem Gbinom_tail_rec
    {R : Type _} [CommSemiring R]
    (d r : ℕ) (x u : R) (hr : r < d) :
    GTail d r x u =
      (Nat.choose d r : R) * u ^ (d - r) + x * GTail d (r + 1) x u :=
  GTail_rec d r x u hr

/--
The `r = 1` tail is the usual one-gap normalized sum.

This is the direct expansion shape that will later serve as the wrapper target
for the legacy `GN`.
-/
theorem GTail_one_eq_sum
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) :
    GTail d 1 x u =
      ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k) := by
  unfold GTail
  rw [show d + 1 - 1 = d by omega]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < d := Finset.mem_range.mp hk
  have hsub : d - (k + 1) = d - 1 - k := by
    omega
  rw [Nat.add_comm 1 k, hsub]

/-- Evaluating the tail at `x = 0` returns its leading coefficient term. -/
theorem GTail_eval_zero
    {R : Type _} [CommSemiring R]
    (d r : ℕ) (u : R) :
    GTail d r 0 u = (Nat.choose d r : R) * u ^ (d - r) := by
  by_cases hr : r ≤ d
  · unfold GTail
    have hlen : d + 1 - r = (d - r) + 1 := by omega
    rw [hlen, Finset.sum_range_succ']
    simp
  · have hdlt : d < r := Nat.lt_of_not_ge hr
    unfold GTail
    have hlen : d + 1 - r = 0 := by omega
    rw [hlen]
    simp [Nat.choose_eq_zero_of_lt hdlt]

/--
Migration alias for evaluating the higher tail at `x = 0`.

This keeps the candidate-notes vocabulary available while `GTail` becomes the
single canonical family.
-/
theorem Gbinom_zero_eval
    {R : Type _} [CommSemiring R]
    (d r : ℕ) (u : R) :
    GTail d r 0 u = (Nat.choose d r : R) * u ^ (d - r) :=
  GTail_eval_zero d r u

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
  rw [Gbinom_tail_rec (R := ℕ) d r x u hr] at htail
  have hmul : p ∣ x * GTail d (r + 1) x u := dvd_mul_of_dvd_left hpx _
  have hhead_dvd : p ∣ Nat.choose d r * u ^ (d - r) :=
    (Nat.dvd_add_right hmul).1 (by simpa [Nat.add_comm] using htail)
  exact hhead hhead_dvd

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

end DkMath.CosmicFormula
