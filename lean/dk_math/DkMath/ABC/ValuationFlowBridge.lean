/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.MassBridge
import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.ValuationFlow.Primitive

#print "file: DkMath.ABC.ValuationFlowBridge"

namespace DkMath.ABC

open DkMath.NumberTheory.ValuationFlow

/--
Minimal package for a finite family of primitive-flow witnesses on a fixed diff.

The support set is a `Finset`, so distinctness is already handled on the index
side.
-/
structure PrimitiveWitnessFamily (a b d : ℕ) where
  support : Finset ℕ
  witness : ∀ q ∈ support, PrimitivePrimeFlowWitness q a b d

/--
Primitive witness viewed as a prime channel on the diff side.

This is the minimal adapter from valuation-flow witnesses to the ABC
support-mass/channel vocabulary.
-/
theorem primitive_witness_gives_prime_channel_on_diff
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d) :
    Nat.Prime q ∧ q ∣ a ^ d - b ^ d := by
  exact ⟨primitivePrimeFlow_prime hq, primitivePrimeFlow_dvd_diff hq⟩

/--
Two distinct primitive witnesses provide two distinct prime channels on the diff
side.
-/
theorem distinct_primitive_witnesses_give_distinct_prime_channels
    {q₁ q₂ a b d : ℕ}
    (hq₁ : PrimitivePrimeFlowWitness q₁ a b d)
    (hq₂ : PrimitivePrimeFlowWitness q₂ a b d)
    (hneq : q₁ ≠ q₂) :
    q₁ ≠ q₂ ∧ Nat.Prime q₁ ∧ Nat.Prime q₂ ∧
      q₁ ∣ a ^ d - b ^ d ∧ q₂ ∣ a ^ d - b ^ d := by
  exact ⟨hneq, primitivePrimeFlow_prime hq₁, primitivePrimeFlow_prime hq₂,
    primitivePrimeFlow_dvd_diff hq₁, primitivePrimeFlow_dvd_diff hq₂⟩

/--
Two distinct primitive channels force a support-mass lower bound on the diff.

This is the primitive-flow shadow of the two-channel lower bound on `rad`.
-/
theorem primitive_channels_force_supportMass_lower_bound
    {q₁ q₂ a b d : ℕ}
    (hq₁ : PrimitivePrimeFlowWitness q₁ a b d)
    (hq₂ : PrimitivePrimeFlowWitness q₂ a b d)
    (hneq : q₁ ≠ q₂)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    q₁ * q₂ ≤ supportMass (a ^ d - b ^ d) := by
  exact supportMass_ge_of_two_distinct_prime_channels
    (n := a ^ d - b ^ d)
    (p := q₁)
    (q := q₂)
    hdiff_ne
    (primitivePrimeFlow_prime hq₁)
    (primitivePrimeFlow_prime hq₂)
    hneq
    (primitivePrimeFlow_dvd_diff hq₁)
    (primitivePrimeFlow_dvd_diff hq₂)

/--
A family of primitive witnesses yields a family of prime channels on the diff
side.

Using a `Finset` of primes keeps distinctness in the index set itself.
-/
theorem primitive_witness_family_gives_prime_channel_family_on_diff
    {a b d : ℕ}
    {S : Finset ℕ}
    (hS : ∀ q ∈ S, PrimitivePrimeFlowWitness q a b d) :
    ∀ q ∈ S, Nat.Prime q ∧ q ∣ a ^ d - b ^ d := by
  intro q hq
  exact primitive_witness_gives_prime_channel_on_diff (hS q hq)

/--
A finite family of primitive witnesses forces the product lower bound on the
support mass of the diff.
-/
theorem primitive_witness_family_force_supportMass_lower_bound
    {a b d : ℕ}
    {S : Finset ℕ}
    (hS : ∀ q ∈ S, PrimitivePrimeFlowWitness q a b d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    S.prod id ≤ supportMass (a ^ d - b ^ d) := by
  exact supportMass_ge_prod_of_prime_channel_family
    (n := a ^ d - b ^ d)
    hdiff_ne
    (primitive_witness_family_gives_prime_channel_family_on_diff hS)

namespace PrimitiveWitnessFamily

/-- The multiplicative size of the packaged prime-channel support. -/
def channelProduct
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d) : ℕ :=
  F.support.prod id

/-- The cardinality of the packaged prime-channel support. -/
def channelCount
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d) : ℕ :=
  F.support.card

/-- The channel product is just the support product, exposed under a bridge name. -/
@[simp] theorem channelProduct_eq_support_prod
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d) :
    F.channelProduct = F.support.prod id := rfl

/-- The channel count is just the support cardinality, exposed under a bridge name. -/
@[simp] theorem channelCount_eq_support_card
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d) :
    F.channelCount = F.support.card := rfl

/--
Read a packaged witness family as a family of prime channels on the diff side.
-/
theorem primeChannelFamily
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d) :
    ∀ q ∈ F.support, Nat.Prime q ∧ q ∣ a ^ d - b ^ d := by
  exact primitive_witness_family_gives_prime_channel_family_on_diff F.witness

/-- Any support member of a packaged witness family is a prime diff channel. -/
theorem mem_support_implies_prime_and_dvd_diff
    {a b d q : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hq : q ∈ F.support) :
    Nat.Prime q ∧ q ∣ a ^ d - b ^ d := by
  exact F.primeChannelFamily q hq

/-- Any support member of a packaged witness family is prime. -/
theorem mem_support_implies_prime_channel
    {a b d q : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hq : q ∈ F.support) :
    Nat.Prime q :=
  (F.mem_support_implies_prime_and_dvd_diff hq).1

/-- Any support member of a packaged witness family divides the diff. -/
theorem mem_support_implies_dvd_diff
    {a b d q : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hq : q ∈ F.support) :
    q ∣ a ^ d - b ^ d :=
  (F.mem_support_implies_prime_and_dvd_diff hq).2

/-- Any support member of a packaged witness family is at least `2`. -/
theorem mem_support_implies_two_le
    {a b d q : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hq : q ∈ F.support) :
    2 ≤ q :=
  (F.mem_support_implies_prime_channel hq).two_le

/--
Generic counting lemma: if every support member is at least `2`, then the
product dominates `2 ^ card`.
-/
private theorem two_pow_card_le_prod_of_two_le
    {S : Finset ℕ} :
    (∀ q ∈ S, 2 ≤ q) → 2 ^ S.card ≤ S.prod id := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro p s hp ih hS
    have hp_two : 2 ≤ p := hS p (by simp [hp])
    have hs_two : ∀ q ∈ s, 2 ≤ q := by
      intro q hq
      exact hS q (by simp [hq])
    have ih' : 2 ^ s.card ≤ s.prod id := ih hs_two
    calc
      2 ^ (Finset.card (insert p s)) = 2 ^ s.card * 2 := by
        simp [hp, Nat.pow_succ]
      _ = 2 * 2 ^ s.card := by rw [Nat.mul_comm]
      _ ≤ p * s.prod id := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.mul_le_mul ih' hp_two)
      _ = (insert p s).prod id := by simp [hp]

/-- The channel count forces a lower bound on the channel product. -/
theorem pow_channelCount_le_channelProduct
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d) :
    2 ^ F.channelCount ≤ F.channelProduct := by
  rw [F.channelCount_eq_support_card, F.channelProduct_eq_support_prod]
  exact two_pow_card_le_prod_of_two_le (fun q hq => F.mem_support_implies_two_le hq)

/--
Packaged witness families inherit the support-mass lower bound on the diff.
-/
theorem supportMassLowerBound
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    F.support.prod id ≤ supportMass (a ^ d - b ^ d) := by
  exact primitive_witness_family_force_supportMass_lower_bound F.witness hdiff_ne

/--
Public-facing alias of the packaged support-mass lower bound, phrased directly
in terms of the channel product.
-/
theorem channelProduct_le_supportMass
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    F.channelProduct ≤ supportMass (a ^ d - b ^ d) := by
  simpa [channelProduct] using F.supportMassLowerBound hdiff_ne

/-- The channel product also gives a lower bound directly on the ABC radical. -/
theorem channelProduct_le_abc_rad_diff
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    F.channelProduct ≤ ABC.rad (a ^ d - b ^ d) := by
  simpa [supportMass_eq_abc_rad] using F.channelProduct_le_supportMass hdiff_ne

/-- The channel count also forces a support-mass lower bound through the product. -/
theorem pow_channelCount_le_supportMass
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    2 ^ F.channelCount ≤ supportMass (a ^ d - b ^ d) := by
  exact le_trans F.pow_channelCount_le_channelProduct
    (F.channelProduct_le_supportMass hdiff_ne)

/-- The counting spine also lands directly in the ABC radical vocabulary. -/
theorem pow_channelCount_le_abc_rad_diff
    {a b d : ℕ}
    (F : PrimitiveWitnessFamily a b d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    2 ^ F.channelCount ≤ ABC.rad (a ^ d - b ^ d) := by
  simpa [supportMass_eq_abc_rad] using F.pow_channelCount_le_supportMass hdiff_ne

end PrimitiveWitnessFamily

/-- Primitive primes contribute no boundary load. -/
theorem primitive_prime_gives_zero_boundary_load
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd1 : 1 < d) :
    boundaryMass q a b = 0 := by
  exact primitivePrimeFlow_boundaryMass_eq_zero hq hd1

/-- Primitive primes transfer all diff load to the beam factor. -/
theorem primitive_prime_transfers_diff_load_to_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    diffMass q a b d = beamMass q a b d := by
  exact primitivePrimeFlow_diffMass_eq_beamMass hq hd hd1 hab_lt

/--
Under a squarefree beam hypothesis, the local diff load is bounded by `1`.
-/
theorem squarefree_beam_bounds_local_load
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq

end DkMath.ABC
