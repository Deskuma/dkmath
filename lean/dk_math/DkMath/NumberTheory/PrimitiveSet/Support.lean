/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.Basic

#print "file: DkMath.NumberTheory.PrimitiveSet.Support"

namespace DkMath.NumberTheory.PrimitiveSet

/--
Finite positivity predicate for natural-number support sets.

This is intentionally separate from `PrimitiveOn`: primitive sets may include
`0` or `1` at the combinatorial layer, while Erdos #1196 support hypotheses
usually impose a positive or lower-bound condition externally.
-/
def PositiveOn (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n

/-- Every member of `S` is at least `x`. -/
def LowerBoundOn (x : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, x ≤ n

namespace PositiveOn

/-- Direct eliminator for membership in a positive support set. -/
theorem pos_of_mem
    {S : Finset ℕ} (hS : PositiveOn S)
    {n : ℕ} (hn : n ∈ S) :
    0 < n :=
  hS n hn

/-- A positive support set cannot contain `0`. -/
theorem not_mem_zero
    {S : Finset ℕ} (hS : PositiveOn S) :
    0 ∉ S := by
  intro h0
  exact (Nat.lt_irrefl 0) (hS 0 h0)

end PositiveOn

namespace LowerBoundOn

/-- Direct eliminator for membership in a lower-bounded support set. -/
theorem le_of_mem
    {x : ℕ} {S : Finset ℕ} (hS : LowerBoundOn x S)
    {n : ℕ} (hn : n ∈ S) :
    x ≤ n :=
  hS n hn

/-- A stronger lower bound implies any weaker lower bound. -/
theorem mono_left
    {x y : ℕ} {S : Finset ℕ}
    (hxy : x ≤ y) (hS : LowerBoundOn y S) :
    LowerBoundOn x S := by
  intro n hn
  exact hxy.trans (hS n hn)

/-- Lower bound by `1` is the same support-side information as positivity. -/
theorem positiveOn_of_one_le
    {S : Finset ℕ} (hS : LowerBoundOn 1 S) :
    PositiveOn S := by
  intro n hn
  exact hS n hn

/-- A set lower-bounded by `1` cannot contain `0`. -/
theorem not_mem_zero_of_one_le
    {S : Finset ℕ} (hS : LowerBoundOn 1 S) :
    0 ∉ S :=
  (positiveOn_of_one_le hS).not_mem_zero

/-- A set lower-bounded by `2` cannot contain `1`. -/
theorem not_mem_one_of_two_le
    {S : Finset ℕ} (hS : LowerBoundOn 2 S) :
    1 ∉ S := by
  intro h1
  have hle : 2 ≤ 1 := hS 1 h1
  norm_num at hle

end LowerBoundOn

/-- Top-level alias: lower bound by `1` implies positivity. -/
theorem lowerBoundOn_one_implies_positiveOn
    {S : Finset ℕ} (hS : LowerBoundOn 1 S) :
    PositiveOn S :=
  LowerBoundOn.positiveOn_of_one_le hS

/-- Top-level alias: positive support excludes `0`. -/
theorem not_mem_zero_of_positiveOn
    {S : Finset ℕ} (hS : PositiveOn S) :
    0 ∉ S :=
  hS.not_mem_zero

/-- Top-level alias: lower bound by `2` excludes `1`. -/
theorem not_mem_one_of_lowerBoundOn_two
    {S : Finset ℕ} (hS : LowerBoundOn 2 S) :
    1 ∉ S :=
  LowerBoundOn.not_mem_one_of_two_le hS

/-- The empty support set is positive. -/
theorem positiveOn_empty :
    PositiveOn (∅ : Finset ℕ) := by
  intro n hn
  simp at hn

/-- The empty support set has every lower bound. -/
theorem lowerBoundOn_empty (x : ℕ) :
    LowerBoundOn x (∅ : Finset ℕ) := by
  intro n hn
  simp at hn

/-- Singleton support positivity. -/
theorem positiveOn_singleton
    {n : ℕ} (hn : 0 < n) :
    PositiveOn ({n} : Finset ℕ) := by
  intro m hm
  simp only [Finset.mem_singleton] at hm
  subst m
  exact hn

/-- Singleton lower-bound support. -/
theorem lowerBoundOn_singleton
    {x n : ℕ} (hxn : x ≤ n) :
    LowerBoundOn x ({n} : Finset ℕ) := by
  intro m hm
  simp only [Finset.mem_singleton] at hm
  subst m
  exact hxn

/-- Concrete lower-bound sample used by later primitive finite examples. -/
theorem lowerBoundOn_pair_two_five :
    LowerBoundOn 2 ({2, 5} : Finset ℕ) := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> norm_num

/-- Concrete positivity sample derived from the lower-bound support API. -/
theorem positiveOn_pair_two_five :
    PositiveOn ({2, 5} : Finset ℕ) :=
  lowerBoundOn_one_implies_positiveOn
    (LowerBoundOn.mono_left (by norm_num) lowerBoundOn_pair_two_five)

end DkMath.NumberTheory.PrimitiveSet
