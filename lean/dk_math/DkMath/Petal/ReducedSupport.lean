/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Basic

#print "file: DkMath.Petal.ReducedSupport"

/-!
# Petal Reduced Support

This file introduces a small support vocabulary for later anchor-prime
observations.

It deliberately does not import the `S0` / `GN` bridge files.  The first layer
only says that a carrier has no prime support below a chosen anchor, and that
the anchor prime itself divides the carrier.
-/

namespace DkMath
namespace Petal

/--
`n` has no prime divisor below `r`.

This is the reduced-support predicate for an `r`-started observation world.
-/
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, Nat.Prime p → p < r → ¬ p ∣ n

/--
`r` is the anchor prime of the carrier `n`.

This means `r` is prime, `r` divides `n`, and no smaller prime divides `n`.
-/
def HasAnchorPrime (r n : ℕ) : Prop :=
  Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n

/-- The anchor in `HasAnchorPrime r n` is prime. -/
theorem hasAnchorPrime_prime
    {r n : ℕ} (h : HasAnchorPrime r n) :
    Nat.Prime r :=
  h.1

/-- The anchor in `HasAnchorPrime r n` divides the carrier. -/
theorem hasAnchorPrime_anchor_dvd
    {r n : ℕ} (h : HasAnchorPrime r n) :
    r ∣ n :=
  h.2.1

/-- No prime below the anchor divides the carrier. -/
theorem hasAnchorPrime_no_smaller_prime
    {r n p : ℕ} (h : HasAnchorPrime r n)
    (hp : Nat.Prime p) (hpr : p < r) :
    ¬ p ∣ n :=
  h.2.2 p hp hpr

end Petal
end DkMath
