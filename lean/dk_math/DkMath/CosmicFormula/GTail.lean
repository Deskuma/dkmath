 /-
 Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
 Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/

import Mathlib

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

end DkMath.CosmicFormula
