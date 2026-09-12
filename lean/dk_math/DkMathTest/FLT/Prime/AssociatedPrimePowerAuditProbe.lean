/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.PowerFactor

#print "file: DkMathTest.FLT.Prime.AssociatedPrimePowerAuditProbe"

namespace DkMathTest.FLT.Prime

/-! The first probe keeps coprime-factor extraction independent of a fixed
exponent and of any quadratic-order implementation. -/

example
    {R : Type*} [CommMonoidWithZero R] [GCDMonoid R]
    {p : ℕ} {x y z : R}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ p) :
    ∃ gamma : R, Associated x (gamma ^ p) := by
  exact DkMath.Lib.NumberTheory.associated_prime_power_of_coprime_mul_eq_pow hcop hpow

/-! Unit absorption is a separate statement.  The hypothesis is phrased on
the unit group so that no inverse or cancellation property is hidden in the
helper itself. -/

example
    {R : Type*} [CommMonoidWithZero R]
    {p : ℕ} {x gamma : R}
    (hassoc : Associated x (gamma ^ p))
    (hsurj : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p) :
    ∃ delta : R, x = delta ^ p := by
  exact DkMath.Lib.NumberTheory.eq_pow_of_associated_pow_of_unit_pow_surjective
    hassoc hsurj

end DkMathTest.FLT.Prime
