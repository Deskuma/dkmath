/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.NumberTheory.PrimitiveSet.Basic"

namespace DkMath.NumberTheory.PrimitiveSet

/--
Finite primitive set predicate for natural numbers.

This is the divisibility-antichain vocabulary used before the analytic
Erdos #1196 layer.  The predicate is intentionally finite and does not remove
`0` by definition: if a positive member and `0` are both present, primitivity
fails because every positive natural divides `0`.
-/
def PrimitiveOn (S : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ S → b ∈ S → a ∣ b → a = b

namespace PrimitiveOn

/-- Direct eliminator for a divisibility relation inside a primitive set. -/
theorem eq_of_dvd
    {S : Finset ℕ} (hS : PrimitiveOn S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ∣ b) :
    a = b :=
  hS ha hb hab

/-- Alias with the pair wording used in the Erdos #1196 notes. -/
theorem pair_eq_of_dvd
    {S : Finset ℕ} (hS : PrimitiveOn S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ∣ b) :
    a = b :=
  hS.eq_of_dvd ha hb hab

/-- Distinct members of a primitive set do not divide each other. -/
theorem not_dvd_of_ne
    {S : Finset ℕ} (hS : PrimitiveOn S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    ¬ a ∣ b := by
  intro hab
  exact hne (hS.eq_of_dvd ha hb hab)

/-- Divisibility inside a primitive set is equivalent to equality. -/
theorem dvd_iff_eq
    {S : Finset ℕ} (hS : PrimitiveOn S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    a ∣ b ↔ a = b := by
  constructor
  · intro hab
    exact hS.eq_of_dvd ha hb hab
  · intro h
    subst h
    exact dvd_rfl

end PrimitiveOn

/-- The empty finite set is primitive. -/
theorem primitiveOn_empty :
    PrimitiveOn (∅ : Finset ℕ) := by
  intro a _ ha
  simp at ha

/-- A singleton finite set is primitive, including the singleton `{0}`. -/
theorem primitiveOn_singleton (a : ℕ) :
    PrimitiveOn ({a} : Finset ℕ) := by
  intro x y hx hy _hxy
  simp only [Finset.mem_singleton] at hx hy
  rw [hx, hy]

/-- A pair is primitive when neither side divides the other. -/
theorem primitiveOn_pair
    {a b : ℕ} (hab : ¬ a ∣ b) (hba : ¬ b ∣ a) :
    PrimitiveOn ({a, b} : Finset ℕ) := by
  intro x y hx hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · rfl
    · exact False.elim (hab hxy)
  · rcases hy with rfl | rfl
    · exact False.elim (hba hxy)
    · rfl

/-- Concrete sample: `{2, 3}` is primitive. -/
theorem primitiveOn_pair_two_three :
    PrimitiveOn ({2, 3} : Finset ℕ) := by
  exact primitiveOn_pair (by norm_num) (by norm_num)

end DkMath.NumberTheory.PrimitiveSet
