/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach.CrossGapExchange
import DkMath.NumberTheory.Goldbach.Obstruction

#print "file: DkMath.NumberTheory.Goldbach.CrossGapEscape"

/-!
# Cross-Gap finite obstruction escape

This module supplies the certification endpoint for a fixed even Cross-Gap
fiber.  It does not provide a survivor and does not encode primality in the
structural predicates.
-/

namespace DkMath.NumberTheory.GoldbachCrossGapEscape

open DkMath.NumberTheory.GoldbachCrossGapExchange

/-- A Cross-Gap configuration on an even fiber with eligible endpoints. -/
def CrossGapEvenFiberAt (n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : Prop :=
  pairedBig d₁ x₁ u₁ d₂ x₂ u₂ = 2 * n ∧
    2 ≤ crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ∧
    2 ≤ crossRight d₁ x₁ u₁ d₂ x₂ u₂

instance (n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    Decidable (CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) := by
  unfold CrossGapEvenFiberAt
  infer_instance

/-- A small prime is a proper obstruction of at least one Cross-Gap endpoint. -/
def CrossGapProperObstructed
    (r d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : Prop :=
  (r ∣ crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ∧
      crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≠ r) ∨
    (r ∣ crossRight d₁ x₁ u₁ d₂ x₂ u₂ ∧
      crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≠ r)

instance (r d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    Decidable (CrossGapProperObstructed r d₁ x₁ u₁ d₂ x₂ u₂) := by
  unfold CrossGapProperObstructed
  infer_instance

/-- Complete small-prime survival for a fixed Cross-Gap even fiber. -/
def CrossGapSurvives
    (n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : Prop :=
  ∀ r ∈ goldbachSmallPrimes n,
    ¬ CrossGapProperObstructed r d₁ x₁ u₁ d₂ x₂ u₂

instance (n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    Decidable (CrossGapSurvives n d₁ x₁ u₁ d₂ x₂ u₂) := by
  unfold CrossGapSurvives
  infer_instance

/-- The first Cross-Gap endpoint lies below the fixed even target. -/
theorem crossLeft_le_even_target_of_fiber
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤ 2 * n := by
  rcases hfiber with ⟨hpaired, hleft, hright⟩
  have htotal :=
    crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂
  omega

/-- The second Cross-Gap endpoint lies below the fixed even target. -/
theorem crossRight_le_even_target_of_fiber
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤ 2 * n := by
  rcases hfiber with ⟨hpaired, hleft, hright⟩
  have htotal :=
    crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂
  omega

/-- Failure of a Cross-Gap prime pair is exactly a finite proper obstruction. -/
theorem crossGap_not_prime_pair_iff_obstructed
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    ¬ (Nat.Prime (crossLeft d₁ x₁ u₁ d₂ x₂ u₂) ∧
      Nat.Prime (crossRight d₁ x₁ u₁ d₂ x₂ u₂)) ↔
      ∃ r ∈ goldbachSmallPrimes n,
        CrossGapProperObstructed r d₁ x₁ u₁ d₂ x₂ u₂ := by
  rcases hfiber with ⟨hpaired, hleft, hright⟩
  have hleft_upper :=
    crossLeft_le_even_target_of_fiber ⟨hpaired, hleft, hright⟩
  have hright_upper :=
    crossRight_le_even_target_of_fiber ⟨hpaired, hleft, hright⟩
  constructor
  · intro h
    by_cases hleft_prime : Nat.Prime (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
    · have hright_not_prime : ¬ Nat.Prime (crossRight d₁ x₁ u₁ d₂ x₂ u₂) := by
        intro hright_prime
        exact h ⟨hleft_prime, hright_prime⟩
      obtain ⟨r, hr, hdiv, hne⟩ :=
        goldbach_small_prime_witness hright hright_upper hright_not_prime
      exact ⟨r, hr, Or.inr ⟨hdiv, hne⟩⟩
    · obtain ⟨r, hr, hdiv, hne⟩ :=
        goldbach_small_prime_witness hleft hleft_upper hleft_prime
      exact ⟨r, hr, Or.inl ⟨hdiv, hne⟩⟩
  · rintro ⟨r, hr, hobs⟩ ⟨hleft_prime, hright_prime⟩
    have hr_prime := (mem_goldbachSmallPrimes.mp hr).1
    exact hobs.elim
      (goldbach_no_proper_divisor_of_prime hleft_prime hr_prime)
      (goldbach_no_proper_divisor_of_prime hright_prime hr_prime)

/-- Complete finite survival is equivalent to primality of both endpoints. -/
theorem crossGapSurvives_iff_prime_pair
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    CrossGapSurvives n d₁ x₁ u₁ d₂ x₂ u₂ ↔
      Nat.Prime (crossLeft d₁ x₁ u₁ d₂ x₂ u₂) ∧
        Nat.Prime (crossRight d₁ x₁ u₁ d₂ x₂ u₂) := by
  have hfailure := crossGap_not_prime_pair_iff_obstructed hfiber
  unfold CrossGapSurvives
  constructor
  · intro hsurvives
    by_contra hnot
    obtain ⟨r, hr, hobs⟩ := hfailure.mp hnot
    exact hsurvives r hr hobs
  · intro hprime r hr hobs
    exact (hfailure.mpr ⟨r, hr, hobs⟩) hprime

/-- One Cross-Gap survivor is enough to produce a Goldbach prime pair. -/
theorem goldbachPairAt_of_crossGapSurvives
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂)
    (hsurvives : CrossGapSurvives n d₁ x₁ u₁ d₂ x₂ u₂) :
    GoldbachPairAt n := by
  have hprime := (crossGapSurvives_iff_prime_pair hfiber).mp hsurvives
  rcases hfiber with ⟨hpaired, hleft, hright⟩
  have htotal :=
    crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂
  refine ⟨crossLeft d₁ x₁ u₁ d₂ x₂ u₂,
    crossRight d₁ x₁ u₁ d₂ x₂ u₂, hprime.1, hprime.2, ?_⟩
  omega

end DkMath.NumberTheory.GoldbachCrossGapEscape
