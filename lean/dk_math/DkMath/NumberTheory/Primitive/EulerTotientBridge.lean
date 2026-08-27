/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Totient
import DkMath.NumberTheory.Primitive.PrimeWorldCardinality

#print "file: DkMath.NumberTheory.Primitive.EulerTotientBridge"

/-!
## Euler-totient identification for finite prime-world residues

`primeWorldResidues S` is DkMath's canonical finite reduced-residue space for
the modulus `primeWorldModulus S`.  Mathlib's `Nat.totient` gives the standard
cardinality name for the same coprime residue space.  This module is only a
bridge between those two descriptions.

In particular, the finite product formula was proved earlier from the
DkMath refinement recurrence.  The totient theorems below identify that
already-established count; they do not use totient multiplicativity or a
squarefree totient formula as a proof engine.  Residue-space membership still
does not assert primality.
-/

namespace DkMath.NumberTheory.Primitive

open scoped BigOperators
open DkMath.NumberTheory.StructuralArithmetic

/-- The canonical residue space and `Nat.totient` count the same finite set. -/
theorem card_primeWorldResidues_eq_totient (S : Finset ℕ) :
    (primeWorldResidues S).card =
      Nat.totient (primeWorldModulus S) := by
  simpa [primeWorldResidues, Nat.coprime_comm] using
    (Nat.totient_eq_card_coprime (primeWorldModulus S)).symm

/-- The DkMath product formula, expressed in Euler-totient vocabulary. -/
theorem totient_primeWorldModulus_eq_prod_sub_one
    {S : Finset ℕ}
    (hS : KnownPrimeScales S) :
    Nat.totient (primeWorldModulus S) =
      ∏ p ∈ S, (p - 1) := by
  calc
    Nat.totient (primeWorldModulus S) =
        (primeWorldResidues S).card :=
      (card_primeWorldResidues_eq_totient S).symm
    _ = ∏ p ∈ S, (p - 1) :=
      card_primeWorldResidues_eq_prod_sub_one hS

/-- The totient product formula specialized to the bounded prime world. -/
theorem totient_primeWorldModulus_primeScalesUpTo (P : ℕ) :
    Nat.totient (primeWorldModulus (primeScalesUpTo P)) =
      ∏ p ∈ primeScalesUpTo P, (p - 1) :=
  totient_primeWorldModulus_eq_prod_sub_one
    (knownPrimeScales_primeScalesUpTo P)

/-- Fresh-prime refinement recurrence rewritten in totient vocabulary. -/
theorem totient_primeWorldModulus_insert
    {S : Finset ℕ}
    (hS : KnownPrimeScales S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    Nat.totient (primeWorldModulus (insert q S)) =
      Nat.totient (primeWorldModulus S) * (q - 1) := by
  calc
    Nat.totient (primeWorldModulus (insert q S)) =
        (primeWorldResidues (insert q S)).card :=
      (card_primeWorldResidues_eq_totient (insert q S)).symm
    _ = (primeWorldResidues S).card * (q - 1) :=
      card_primeWorldResidues_insert hS hq hqS
    _ = Nat.totient (primeWorldModulus S) * (q - 1) := by
      rw [card_primeWorldResidues_eq_totient]

end DkMath.NumberTheory.Primitive
