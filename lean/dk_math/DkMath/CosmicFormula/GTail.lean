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
`r = 1` recursion in the canonical `GN` vocabulary.

This is the `GTail_rec` specialization that matches the standard one-gap
normalized kernel naming.
-/
theorem GN_tail_rec
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) (hd : 1 < d) :
    GTail d 1 x u =
      (Nat.choose d 1 : R) * u ^ (d - 1) + x * GTail d 2 x u := by
  simpa using GTail_rec d 1 x u hd

/--
Compatibility alias matching the implementation-plan naming.
-/
theorem GN_tail_decomposition
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) (hd : 1 < d) :
    GTail d 1 x u =
      (Nat.choose d 1 : R) * u ^ (d - 1) + x * GTail d 2 x u :=
  GN_tail_rec d x u hd

/--
Compatibility alias for the old `Gbinom`-flavored recursion name.

[GNZC] New code should prefer `GN_tail_rec`.
-/
theorem Gbinom_tail_rec
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) (hd : 1 < d) :
    GTail d 1 x u =
      (Nat.choose d 1 : R) * u ^ (d - 1) + x * GTail d 2 x u :=
  GN_tail_rec d x u hd

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
`r = 1` zero-evaluation in the canonical `GN` vocabulary.
-/
theorem GN_zero_eval
    {R : Type _} [CommSemiring R]
    (d : ℕ) (u : R) :
    GTail d 1 0 u = (Nat.choose d 1 : R) * u ^ (d - 1) :=
  GTail_eval_zero d 1 u

/--
Compatibility alias for the old `Gbinom`-flavored zero-evaluation name.

[GNZC] New code should prefer `GN_zero_eval`.
-/
theorem Gbinom_zero_eval
    {R : Type _} [CommSemiring R]
    (d : ℕ) (u : R) :
    GTail d 1 0 u = (Nat.choose d 1 : R) * u ^ (d - 1) :=
  GN_zero_eval d u

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

/-!
### Congruence properties of the tail family

The following theorems concern the behavior of `GTail d r x u` modulo a
natural number `n`, particularly when `n ∣ x`.  They are independent of any
FLT hypothesis and hold for arbitrary naturals in the intended range.

**Key pattern**: since `GTail d r x u` is a polynomial in `x` and `u`,
congruences in `x` and `u` propagate to congruences in the tail value.
When `n ∣ x` (i.e., `x ≡ 0 [MOD n]`), the tail collapses to the
`x = 0` evaluation, which equals `C(d,r) * u^{d-r}` by `GTail_eval_zero`.
-/

/--
Congruence propagation for `GTail`: if `x ≡ x' [MOD n]` and `u ≡ u' [MOD n]`,
then `GTail d r x u ≡ GTail d r x' u' [MOD n]`.

This follows from the polynomial nature of `GTail` — each term
`C(d, r+k) * x^k * u^{d-(r+k)}` is a monomial in `x` and `u`,
and congruences compose multiplicatively.
-/
private theorem sum_range_modEq
    {m n : ℕ} {f g : ℕ → ℕ}
    (hfg : ∀ i, i < m → f i ≡ g i [MOD n]) :
    ((Finset.range m).sum f) ≡ ((Finset.range m).sum g) [MOD n] := by
  induction m with
  | zero =>
      exact Nat.ModEq.rfl
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (ih (by
        intro i hi
        exact hfg i (Nat.lt_succ_of_lt hi))).add (hfg m (Nat.lt_succ_self m))

theorem GTail_congr_of_modEq
    {n d r : ℕ} {x x' u u' : ℕ}
    (hx : x ≡ x' [MOD n])
    (hu : u ≡ u' [MOD n]) :
    GTail d r x u ≡ GTail d r x' u' [MOD n] := by
  unfold GTail
  refine sum_range_modEq ?_
  intro k hk
  have hxk : x ^ k ≡ x' ^ k [MOD n] := hx.pow k
  have huk : u ^ (d - (r + k)) ≡ u' ^ (d - (r + k)) [MOD n] := hu.pow (d - (r + k))
  have hmul : x ^ k * u ^ (d - (r + k)) ≡ x' ^ k * u' ^ (d - (r + k)) [MOD n] :=
    hxk.mul huk
  simpa [mul_assoc] using (hmul.mul_left (Nat.choose d (r + k)))

/--
When `x ≡ 0 [MOD n]`, the tail `GTail d r x u` is congruent to
`GTail d r 0 u`, which equals `C(d,r) * u^{d-r}` by `GTail_eval_zero`.
-/
theorem GTail_modEq_eval_zero_of_dvd_x
    {n d r : ℕ} (x u : ℕ)
    (hpx : n ∣ x) :
    GTail d r x u ≡ GTail d r 0 u [MOD n] :=
  GTail_congr_of_modEq (Nat.modEq_zero_iff_dvd.mpr hpx) (Nat.ModEq.refl u)

/--
Under `n ∣ x`, the normalized `GN` tail is congruent to
`C(d, 1) * u^{d-1}` modulo `n`.

This is the fundamental "mod-`n` collapse" of the cosmic formula:
`GN d x u ≡ d * u^{d-1} [MOD n]` when `n ∣ x`
(using `Nat.choose d 1 = d`).

**Concrete applications**:
- `n = p` prime, `p ∣ x`, `p ∤ u` ⟹ `p ∣ GN d x u` iff `p ∣ d * u^{d-1}`
- `n = d` ⟹ `GN d x u ≡ 0 [MOD d]` (since `d ∣ d * u^{d-1}`)

Valid for any `d ≥ 1` and any modulus `n ∣ x`.
-/
theorem GN_modEq_choose_mul_pow_of_dvd_x
    {d n : ℕ} (x u : ℕ)
    (_hd : 1 ≤ d) (hnx : n ∣ x) :
    GTail d 1 x u ≡ Nat.choose d 1 * u ^ (d - 1) [MOD n] := by
  have h0 := GTail_modEq_eval_zero_of_dvd_x x u hnx (d := d) (r := 1)
  rw [GTail_eval_zero d 1 u] at h0
  exact h0

-- The clean version without the circular hypothesis:

/--
Under `n ∣ x`, the normalized GN tail satisfies
`GTail d 1 x u ≡ Nat.choose d 1 * u^{d-1} [MOD n]`.

This uses `GTail_modEq_eval_zero_of_dvd_x` + `GTail_eval_zero`.
-/
theorem GN_modEq_head_of_dvd_x
    {d n : ℕ} (x u : ℕ)
    (hdpos : 1 ≤ d)
    (hnx : n ∣ x) :
    GTail d 1 x u ≡ Nat.choose d 1 * u ^ (d - 1) [MOD n] := by
  exact GN_modEq_choose_mul_pow_of_dvd_x x u hdpos hnx

/--
Specialization: when `d` is itself the modulus and `d ∣ x`, then
`GTail d 1 x u ≡ d * u^{d-1} [MOD d]`.

Uses `Nat.choose d 1 = d`.
-/
theorem GN_modEq_mul_pow_self_of_dvd_x
    {d : ℕ} (x u : ℕ)
    (hdpos : 1 ≤ d)
    (hdx : d ∣ x) :
    GTail d 1 x u ≡ d * u ^ (d - 1) [MOD d] := by
  have h := GN_modEq_head_of_dvd_x x u hdpos hdx
  simpa [Nat.choose_one_right] using h

/--
When `p` is prime and `p ∣ x`, then `GN p x u ≡ p * u^{p-1} [MOD p^2]`.

**Proof sketch**:
- `GN_tail_rec`: `GTail p 1 x u = p * u^{p-1} + x * GTail p 2 x u`
- The second term: `x * GTail p 2 x u = x * (C(p,2) * u^{p-2} + x * GTail p 3 x u)`
- `p ∣ x` gives one factor of `p` from `x`.
- `C(p,2) = p*(p-1)/2` provides a second factor of `p`
  (since `p` is an odd prime, `p ∣ C(p,2)`).
- Hence `p^2 ∣ x * C(p,2) * u^{p-2}` and `p^2 ∣ x^2 * ...`.
- Together: `p^2 ∣ x * GTail p 2 x u`, so the remainder vanishes mod `p^2`.

This is the `mod p^2` version of the cosmic formula collapse, used in
Branch A's Wieferich analysis: combined with `GN = p * s^p`,
it yields `s^p ≡ u^{p-1} [MOD p^2]`.
-/
theorem GN_modEq_head_mod_sq_of_prime_dvd_x
    {p : ℕ} (x u : ℕ)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpx : p ∣ x) :
    GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 2] := by
  have hlt : 1 < p := hp.one_lt
  -- expand: GTail p 1 = p * u^{p-1} + x * GTail p 2
  rw [GN_tail_rec p x u hlt]
  simp only [Nat.choose_one_right]
  -- it suffices to show p^2 ∣ x * GTail p 2 x u
  suffices h : p ^ 2 ∣ x * GTail p 2 x u by
    change (p * u ^ (p - 1) + x * GTail p 2 x u) % p ^ 2 = (p * u ^ (p - 1)) % p ^ 2
    have hmod := Nat.dvd_iff_mod_eq_zero.mp h
    rw [Nat.add_mod, hmod, Nat.add_zero, Nat.mod_mod]
  -- expand GTail p 2: C(p,2) * u^{p-2} + x * GTail p 3
  have hGTail2 : GTail p 2 x u =
      (Nat.choose p 2 : ℕ) * u ^ (p - 2) + x * GTail p 3 x u :=
    GTail_rec p 2 x u (by omega)
  rw [hGTail2]
  have hchoose2 : p ∣ Nat.choose p 2 :=
    hp.dvd_choose_self (by omega) (by omega)
  have h1 : p ^ 2 ∣ x * (Nat.choose p 2 * u ^ (p - 2)) := by
    have hpp : p ^ 2 ∣ x * Nat.choose p 2 :=
      pow_two p ▸ Nat.mul_dvd_mul hpx hchoose2
    have : x * (Nat.choose p 2 * u ^ (p - 2)) = x * Nat.choose p 2 * u ^ (p - 2) := by ring
    rw [this]
    exact dvd_mul_of_dvd_left hpp _
  have h2 : p ^ 2 ∣ x * (x * GTail p 3 x u) := by
    have : x * (x * GTail p 3 x u) = x * x * GTail p 3 x u := by ring
    rw [this]
    exact dvd_mul_of_dvd_left (pow_two p ▸ Nat.mul_dvd_mul hpx hpx) _
  have heq : x * (Nat.choose p 2 * u ^ (p - 2) + x * GTail p 3 x u) =
      x * (Nat.choose p 2 * u ^ (p - 2)) + x * (x * GTail p 3 x u) := by ring
  rw [heq]
  exact Nat.dvd_add h1 h2

/--
Plan-name alias: `mod p^2` head congruence for `GN`.
-/
theorem GN_mod_p2_head
    {p : ℕ} (x u : ℕ)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpx : p ∣ x) :
    GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 2] :=
  GN_modEq_head_mod_sq_of_prime_dvd_x x u hp hp5 hpx

/--
`mod p^2` congruence rewritten as a concrete equality with an explicit tail.
-/
theorem GN_eq_head_add_p_sq_mul_of_prime_dvd_x
    {p : ℕ} (x u : ℕ)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpx : p ∣ x) :
    ∃ M : ℕ, GTail p 1 x u = p * u ^ (p - 1) + p ^ 2 * M := by
  have hmod : GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 2] :=
    GN_modEq_head_mod_sq_of_prime_dvd_x x u hp hp5 hpx
  have hle : p * u ^ (p - 1) ≤ GTail p 1 x u := by
    rw [GN_tail_rec p x u hp.one_lt]
    simp [Nat.choose_one_right]
  have hdiv : p ^ 2 ∣ GTail p 1 x u - (p * u ^ (p - 1)) :=
    (Nat.modEq_iff_dvd' hle).mp hmod.symm
  rcases exists_eq_mul_left_of_dvd hdiv with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  calc
    GTail p 1 x u = p * u ^ (p - 1) + (GTail p 1 x u - (p * u ^ (p - 1))) := by
      exact (Nat.add_sub_of_le hle).symm
    _ = p * u ^ (p - 1) + p ^ 2 * M := by
      rw [hM]
      ring

/--
Plan-name `mod p^3` head congruence under an explicit third-order tail divisibility hypothesis.
-/
theorem GN_mod_p3_head
    {p : ℕ} (x u : ℕ)
    (hp1 : 1 < p)
    (htail : p ^ 3 ∣ x * GTail p 2 x u) :
    GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 3] := by
  rw [GN_tail_rec p x u hp1]
  simp only [Nat.choose_one_right]
  change (p * u ^ (p - 1) + x * GTail p 2 x u) % p ^ 3 = (p * u ^ (p - 1)) % p ^ 3
  have hmod := Nat.dvd_iff_mod_eq_zero.mp htail
  rw [Nat.add_mod, hmod, Nat.add_zero, Nat.mod_mod]

/--
`mod p^3` head congruence rewritten as a concrete equality with an explicit tail.
-/
theorem GN_eq_head_add_p_cube_mul_of_dvd_tail
    {p : ℕ} (x u : ℕ)
    (hp1 : 1 < p)
    (htail : p ^ 3 ∣ x * GTail p 2 x u) :
    ∃ M : ℕ, GTail p 1 x u = p * u ^ (p - 1) + p ^ 3 * M := by
  rw [GN_tail_rec p x u hp1]
  simp only [Nat.choose_one_right]
  rcases exists_eq_mul_left_of_dvd htail with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  rw [hM]
  simp [Nat.mul_comm]

end DkMath.CosmicFormula
