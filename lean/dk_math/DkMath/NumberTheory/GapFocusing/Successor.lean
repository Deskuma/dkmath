/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCyclotomic
import Mathlib.RingTheory.Coprime.Basic

#print "file: DkMath.NumberTheory.GapFocusing.Successor"

/-!
# Successor identities for the existing gap-normalized kernel

Both recurrence identities hold in every commutative semiring, including
zero gaps, zero divisors, and degree zero. The unit-anchor identity is a
Bézout witness in every commutative ring; no division by the gap is used.
-/

namespace DkMath.NumberTheory.GapFocusing

open DkMath.CosmicFormula

/-- Successor recurrence retaining the power of the sum coordinate. -/
theorem GN_succ_right {R : Type*} [CommSemiring R] (d : ℕ) (x u : R) :
    GTail (d + 1) 1 x u = u * GTail d 1 x u + (x + u) ^ d := by
  rw [GTail_one_eq_GTailCyclotomicShell,
    GTailCyclotomicShell_succ, GTail_one_eq_GTailCyclotomicShell]

/-- Successor recurrence retaining the anchor power. -/
theorem GN_succ_left {R : Type*} [CommSemiring R] (d : ℕ) (x u : R) :
    GTail (d + 1) 1 x u = (x + u) * GTail d 1 x u + u ^ d := by
  rw [GN_succ_right, add_pow_eq_mul_GTail_one_add_gap]
  ring

/-- At a unit anchor, the recurrence has a constant one remainder. -/
theorem GN_succ_unit_anchor {R : Type*} [CommSemiring R] (d : ℕ) (x : R) :
    GTail (d + 1) 1 x 1 = (x + 1) * GTail d 1 x 1 + 1 := by
  simpa only [one_pow] using GN_succ_left d x (1 : R)

/-- The unit-anchor recurrence is an explicit Bézout identity in any ring. -/
theorem GN_succ_bezout {R : Type*} [CommRing R] (d : ℕ) (x : R) :
    GTail (d + 1) 1 x 1 - (x + 1) * GTail d 1 x 1 = 1 := by
  rw [GN_succ_unit_anchor]
  exact add_sub_cancel_left _ _

/-- Universal unit-anchor coprimality, as a Bézout relation. -/
theorem GN_succ_isCoprime_unit_anchor {R : Type*} [CommRing R] (d : ℕ) (x : R) :
    IsCoprime (GTail d 1 x 1) (GTail (d + 1) 1 x 1) := by
  refine ⟨-(x + 1), 1, ?_⟩
  rw [GN_succ_unit_anchor]
  ring

end DkMath.NumberTheory.GapFocusing
