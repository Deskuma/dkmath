/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

/-!
# Collatz: Basic Definitions

This module provides the fundamental definitions for the accelerated Collatz
conjecture framework:
  - The standard Collatz map C(n) on all naturals
  - The power-of-2 function
  - The odd naturals as a subtype
  - The accelerated Collatz map T(n) on odd naturals (3n+1 divided by 2^v₂(3n+1))
-/

namespace DkMath.Collatz

/-- The standard Collatz map on ℕ.
    C(n) = n/2 if 2 | n, else 3n+1.
-/
def C (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3*n + 1

/-- Power of 2: 2^k -/
def pow2 (k : ℕ) : ℕ := 2^k

/-- The type of odd natural numbers.
    An odd natural is a natural n such that n % 2 = 1.
-/
def OddNat := {n : ℕ // n % 2 = 1}

/-- Constructor for OddNat from a natural known to be odd. -/
def mkOddNat (n : ℕ) (h : n % 2 = 1) : OddNat := ⟨n, h⟩

/-- 3n + 1 for n ∈ ℕ. -/
def threeNPlusOne (n : ℕ) : ℕ := 3 * n + 1

/-- The accelerated Collatz map on odd naturals.
    For odd n, we compute a := 3n+1, then return (a / 2^v₂(a)) as an OddNat.

    The result is always odd because we divide out all factors of 2.
-/
noncomputable def T : OddNat → OddNat := fun n =>
  -- Implementation: divide 3n+1 by its 2-adic valuation power
  -- This requires v2 from V2.lean
  sorry

/-- The observation function: s(n) := v₂(3n+1) for odd n.

    Returns the 2-adic valuation of 3n+1.
-/
noncomputable def s : OddNat → ℕ := fun n =>
  -- Implementation: s(n) = v2(3n+1)
  -- This requires v2 from V2.lean
  sorry

/-- Iterated application of T: iterateT m n represents m applications of T to n. -/
noncomputable def iterateT : ℕ → OddNat → OddNat
| 0, n => n
| m+1, n => iterateT m (T n)

/-- The partial sum of the observation sequence over m steps.
    S_m(n) := ∑_{i=0}^{m-1} s(T^i(n))

    Recursively: sumS(0) = 0, sumS(m+1) = sumS(m) + s(iterateT(m)(n))
-/
noncomputable def sumS : OddNat → ℕ → ℕ
| _, 0 => 0
| n, m+1 => sumS n m + s (iterateT m n)

/-- The drift at step m (up to numeric scale).
    D_m(n) := m·log₂(3) - S_m(n) (in ℝ)

    For now we keep this symbolic; actual numeric computation in Python.
-/
noncomputable def driftReal : OddNat → ℕ → ℝ := fun n m =>
  (m : ℝ) * (Real.log 3 / Real.log 2) - (sumS n m : ℝ)

end DkMath.Collatz
