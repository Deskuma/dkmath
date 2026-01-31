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

end DkMath.Collatz
