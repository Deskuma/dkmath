/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail

/-!
# Pascal surfaces for `GTail`

This module exposes the finite-depth filtration of the canonical `GTail`
kernel.  A tail at depth `r` is split at a later depth `s` into the layers
from `r` through `s - 1` and the normalized tail at `s`.

The result is a finite algebraic identity.  It does not introduce a
Goldbach-specific theorem, a valuation bridge, or an asymptotic statement.
-/

namespace DkMath.CosmicFormula

open scoped BigOperators

/--
Split `GTail d r x u` at any intermediate depth `s`.

The first summand records the layers between `r` and `s`, while the second
summand is the remaining tail with its accumulated `x`-power factored out.
-/
theorem GTail_split_at
    {R : Type _} [CommSemiring R]
    (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d) :
    GTail d r x u =
      (∑ k ∈ Finset.range (s - r),
        (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k)))
        + x ^ (s - r) * GTail d s x u := by
  let f : ℕ → R := fun k =>
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))
  have hsplit :=
    Finset.sum_range_add_sum_Ico f
      (show s - r ≤ d + 1 - r by omega)
  have htail_reindex :
      ∑ j ∈ Finset.Ico (s - r) (d + 1 - r), f j =
        ∑ k ∈ Finset.range (d + 1 - s), f ((s - r) + k) := by
    have hupper : (s - r) + (d + 1 - s) = d + 1 - r := by
      omega
    calc
      ∑ j ∈ Finset.Ico (s - r) (d + 1 - r), f j =
          ∑ j ∈ Finset.Ico (s - r) ((s - r) + (d + 1 - s)), f j := by
            rw [hupper]
      _ = ∑ k ∈ Finset.Ico 0 (d + 1 - s), f (k + (s - r)) := by
            symm
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Finset.sum_Ico_add' f 0 (d + 1 - s) (s - r))
      _ = ∑ k ∈ Finset.range (d + 1 - s), f ((s - r) + k) := by
            rw [Nat.Ico_zero_eq_range]
            apply Finset.sum_congr rfl
            intro k hk
            simp [Nat.add_comm]
  have htail_factor :
      ∑ k ∈ Finset.range (d + 1 - s), f ((s - r) + k) =
        x ^ (s - r) * GTail d s x u := by
    unfold GTail
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hindex : r + ((s - r) + k) = s + k := by
      omega
    dsimp [f]
    rw [hindex]
    simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
  unfold GTail
  calc
    ∑ k ∈ Finset.range (d + 1 - r), f k =
        (∑ k ∈ Finset.range (s - r), f k) +
          ∑ k ∈ Finset.Ico (s - r) (d + 1 - r), f k := by
      rw [← hsplit]
    _ =
        (∑ k ∈ Finset.range (s - r),
          (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))) +
          ∑ k ∈ Finset.range (d + 1 - s), f ((s - r) + k) := by
      rw [htail_reindex]
    _ =
        (∑ k ∈ Finset.range (s - r),
          (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))) +
          x ^ (s - r) * GTail d s x u := by
      rw [htail_factor]

end DkMath.CosmicFormula
