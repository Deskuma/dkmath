/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.ReducedSupport
import DkMath.Petal.GNBridge
import DkMath.Petal.PrimitiveBridge

#print "file: DkMath.Petal.Anchor"

/-!
# Petal Anchor

This file connects the reduced-support vocabulary to the `S0` / `GN` carrier
surfaces.

`ReducedSupport` stays independent of `S0` and `GN`.  This file is the first
bridge layer where a positive anchored carrier is required to divide a concrete
Petal or GN observation target.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom
open DkMath.FLT.PetalDetect

/--
An anchored positive carrier dividing the cubic Petal detector `S0_nat c b`.
-/
def AnchoredS0Carrier (r c b n : ℕ) : Prop :=
  HasPositiveAnchorPrime r n ∧ n ∣ S0_nat c b

/--
An anchored positive carrier dividing the general GN kernel `GN d x u`.
-/
def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
  HasPositiveAnchorPrime r n ∧ n ∣ GN d x u

/-- Extract the positive anchor witness from an anchored `S0_nat` carrier. -/
theorem anchoredS0Carrier_anchor
    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
    HasPositiveAnchorPrime r n :=
  h.1

/-- Extract the divisibility statement from an anchored `S0_nat` carrier. -/
theorem anchoredS0Carrier_dvd_S0
    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
    n ∣ S0_nat c b :=
  h.2

/-- The carrier in an anchored `S0_nat` carrier is positive. -/
theorem anchoredS0Carrier_pos
    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
    0 < n :=
  hasPositiveAnchorPrime_pos h.1

/-- The carrier in an anchored `S0_nat` carrier is nonzero. -/
theorem anchoredS0Carrier_ne_zero
    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
    n ≠ 0 :=
  hasPositiveAnchorPrime_ne_zero h.1

/-- Any prime divisor of an anchored `S0_nat` carrier is at least the anchor. -/
theorem anchoredS0Carrier_anchor_le_of_prime_dvd
    {r c b n p : ℕ} (h : AnchoredS0Carrier r c b n)
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    r ≤ p :=
  hasPositiveAnchorPrime_anchor_le_of_prime_dvd h.1 hp hpdiv

/-- Extract the positive anchor witness from an anchored GN carrier. -/
theorem anchoredGNCarrier_anchor
    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
    HasPositiveAnchorPrime r n :=
  h.1

/-- Extract the divisibility statement from an anchored GN carrier. -/
theorem anchoredGNCarrier_dvd_GN
    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
    n ∣ GN d x u :=
  h.2

/-- The carrier in an anchored GN carrier is positive. -/
theorem anchoredGNCarrier_pos
    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
    0 < n :=
  hasPositiveAnchorPrime_pos h.1

/-- The carrier in an anchored GN carrier is nonzero. -/
theorem anchoredGNCarrier_ne_zero
    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
    n ≠ 0 :=
  hasPositiveAnchorPrime_ne_zero h.1

/-- Any prime divisor of an anchored GN carrier is at least the anchor. -/
theorem anchoredGNCarrier_anchor_le_of_prime_dvd
    {r d x u n p : ℕ} (h : AnchoredGNCarrier r d x u n)
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    r ≤ p :=
  hasPositiveAnchorPrime_anchor_le_of_prime_dvd h.1 hp hpdiv

/--
The degree-three Petal face turns an anchored `S0_nat` carrier into an anchored
GN carrier.
-/
theorem anchoredGNCarrier_of_anchoredS0Carrier
    {r c b n : ℕ} (hbc : b < c)
    (h : AnchoredS0Carrier r c b n) :
    AnchoredGNCarrier r 3 (c - b) b n := by
  refine ⟨h.1, ?_⟩
  rw [← S0_nat_eq_GN_three_sub hbc]
  exact h.2

/--
The degree-three GN face turns an anchored GN carrier into an anchored
`S0_nat` carrier.
-/
theorem anchoredS0Carrier_of_anchoredGNCarrier
    {r c b n : ℕ} (hbc : b < c)
    (h : AnchoredGNCarrier r 3 (c - b) b n) :
    AnchoredS0Carrier r c b n := by
  refine ⟨h.1, ?_⟩
  rw [S0_nat_eq_GN_three_sub hbc]
  exact h.2

/--
Primitive S0 existence, upgraded to an anchored S0 carrier.

If `3` does not divide the boundary gap, then there is a prime `q` such that
`q` is its own positive anchor carrier, `q` divides `S0_nat c b`, and `q` does
not divide the boundary gap.
-/
theorem exists_anchoredS0Carrier_of_not_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b := by
  rcases exists_prime_dvd_S0_nat_of_not_three_dvd_sub hbc hb hcop h3 with
    ⟨q, hq, hq_dvd_S0, hq_not_dvd_sub⟩
  exact ⟨q, ⟨⟨hasPositiveAnchorPrime_self_of_prime hq, hq_dvd_S0⟩, hq_not_dvd_sub⟩⟩

end Petal
end DkMath
