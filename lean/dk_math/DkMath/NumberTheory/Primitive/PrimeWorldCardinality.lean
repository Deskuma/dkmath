/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import DkMath.NumberTheory.Primitive.PrimeWorldResidues

#print "file: DkMath.NumberTheory.Primitive.PrimeWorldCardinality"

/-!
## Cardinality of a finite prime-world residue space

The exact refinement recurrence says that inserting a fresh prime direction
`q` leaves `q - 1` children for each old canonical residue.  Finite-set
induction therefore gives the product formula
`|primeWorldResidues S| = ∏ p in S, (p - 1)`.

This is the internal DkMath refinement count for finite divisibility support.
It does not invoke Euler's totient function and does not turn residue-space
membership into a primality assertion.
-/

namespace DkMath.NumberTheory.Primitive

open scoped BigOperators
open DkMath.NumberTheory.StructuralArithmetic

/-- The empty finite world has the single canonical residue `0`. -/
@[simp] theorem primeWorldResidues_empty :
    primeWorldResidues ∅ = {0} := by
  ext n
  simp [primeWorldResidues, primeWorldModulus]

/-- The empty finite world has one canonical residue. -/
@[simp] theorem card_primeWorldResidues_empty :
    (primeWorldResidues ∅).card = 1 := by
  rw [primeWorldResidues_empty, Finset.card_singleton]

/--
The canonical residue count is the product of the fresh-prime survivor counts.

The insertion step is exactly `card_primeWorldResidues_insert`; the proof does
not repeat the child-coordinate or CRT arguments already established by the
refinement modules.
-/
theorem card_primeWorldResidues_eq_prod_sub_one
    {S : Finset ℕ}
    (hS : KnownPrimeScales S) :
    (primeWorldResidues S).card =
      ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert q S hqS ih =>
      have hq : Nat.Prime q := hS (Finset.mem_insert_self q S)
      have hS' : KnownPrimeScales S := by
        intro p hp
        exact hS (Finset.mem_insert_of_mem hp)
      calc
        (primeWorldResidues (insert q S)).card =
            (primeWorldResidues S).card * (q - 1) :=
          card_primeWorldResidues_insert hS' hq hqS
        _ = (∏ p ∈ S, (p - 1)) * (q - 1) := by rw [ih hS']
        _ = ∏ p ∈ insert q S, (p - 1) := by
          simp [Finset.prod_insert, hqS, Nat.mul_comm]

/-- The product formula specialized to the canonical bounded prime world. -/
theorem card_primeWorldResidues_primeScalesUpTo (P : ℕ) :
    (primeWorldResidues (primeScalesUpTo P)).card =
      ∏ p ∈ primeScalesUpTo P, (p - 1) :=
  card_primeWorldResidues_eq_prod_sub_one
    (knownPrimeScales_primeScalesUpTo P)

end DkMath.NumberTheory.Primitive
