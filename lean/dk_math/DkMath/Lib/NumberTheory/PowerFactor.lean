/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.NumberTheory.PowerFactor"

/-!
# Coprime power-factor splitting

This module contains the generic natural-number wrapper around Mathlib's
`exists_eq_pow_of_mul_eq_pow`.  It is independent of FLT and of any fixed
exponent.
-/

namespace DkMath.Lib.NumberTheory

/-- Coprime factors of a power are powers with the same exponent. -/
theorem power_factor_split
    {d a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ d) :
    (∃ u : ℕ, a = u ^ d) ∧ (∃ v : ℕ, b = v ^ d) := by
  have hunit : IsUnit (GCDMonoid.gcd a b) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd b a) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)

end DkMath.Lib.NumberTheory
