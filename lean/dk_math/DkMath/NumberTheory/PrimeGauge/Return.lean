/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.CycleDivision

#print "file: DkMath.NumberTheory.PrimeGauge.Return"

/-!
# Prime Gauge return and phase bridges

This module exposes the finite arithmetic observer already carried by the
CF2D regular kernel.  It does not add a prime-order structure and it does not
turn a finite phase identity into a primality or Goldbach theorem.
-/

namespace DkMath.NumberTheory.PrimeGauge

open DkMath.CosmicFormula.Rotation.CF2D

/--
The positive `k`-division CF2D kernel returns to one exactly at the multiples
of `k`.

This is a thin arithmetic wrapper around `orderOf_regularKernel` and
Mathlib's `orderOf_dvd_iff_pow_eq_one`.
-/
theorem regularKernel_pow_eq_one_iff_dvd
    {k n : ℕ} (hk : 0 < k) :
    regularKernel k ^ n = 1 ↔ k ∣ n := by
  simpa [orderOf_regularKernel hk] using
    (orderOf_dvd_iff_pow_eq_one (x := regularKernel k) (n := n)).symm

/--
Equality of two powers of the positive `k`-division CF2D kernel is exactly
equality of their natural-number phases modulo `k`.
-/
theorem regularKernel_pow_eq_pow_iff_modEq
    {k a b : ℕ} (hk : 0 < k) :
    regularKernel k ^ a = regularKernel k ^ b ↔ Nat.ModEq k a b := by
  simpa [orderOf_regularKernel hk] using
    (pow_eq_pow_iff_modEq (x := regularKernel k) (n := a) (m := b))

end DkMath.NumberTheory.PrimeGauge

