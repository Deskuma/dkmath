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

This is the raw carrier predicate.  It intentionally does not require `0 < n`;
use `HasPositiveAnchorPrime` when the carrier must be an actual positive
support object.
-/
def HasAnchorPrime (r n : ℕ) : Prop :=
  Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n

/--
Positive version of `HasAnchorPrime`.

Use this for actual prime-support carriers, excluding the special carrier `0`.
-/
def HasPositiveAnchorPrime (r n : ℕ) : Prop :=
  0 < n ∧ HasAnchorPrime r n

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

/--
Any prime divisor of the carrier is at least the anchor.

This is the practical elimination form of `HasNoPrimeBelow`.
-/
theorem hasAnchorPrime_anchor_le_of_prime_dvd
    {r n p : ℕ} (h : HasAnchorPrime r n)
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    r ≤ p := by
  by_contra hnot
  exact h.2.2 p hp (Nat.lt_of_not_ge hnot) hpdiv

/-- The carrier in `HasPositiveAnchorPrime r n` is positive. -/
theorem hasPositiveAnchorPrime_pos
    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
    0 < n :=
  h.1

/-- The anchor in `HasPositiveAnchorPrime r n` is prime. -/
theorem hasPositiveAnchorPrime_prime
    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
    Nat.Prime r :=
  hasAnchorPrime_prime h.2

/-- The anchor in `HasPositiveAnchorPrime r n` divides the carrier. -/
theorem hasPositiveAnchorPrime_anchor_dvd
    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
    r ∣ n :=
  hasAnchorPrime_anchor_dvd h.2

/-- No prime below the positive anchor divides the carrier. -/
theorem hasPositiveAnchorPrime_no_smaller_prime
    {r n p : ℕ} (h : HasPositiveAnchorPrime r n)
    (hp : Nat.Prime p) (hpr : p < r) :
    ¬ p ∣ n :=
  hasAnchorPrime_no_smaller_prime h.2 hp hpr

/-- Any prime divisor of a positive anchored carrier is at least the anchor. -/
theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
    {r n p : ℕ} (h : HasPositiveAnchorPrime r n)
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    r ≤ p :=
  hasAnchorPrime_anchor_le_of_prime_dvd h.2 hp hpdiv

end Petal
end DkMath
