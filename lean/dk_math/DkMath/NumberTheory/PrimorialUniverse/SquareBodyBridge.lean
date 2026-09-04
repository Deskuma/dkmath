/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
import DkMath.NumberTheory.Primitive.SquarePrimeExpansion

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge"

/-!
## Primorial product anchors and fine square worlds

For a finite prime basis S, the product

    A = finitePrimeBasisProduct S

is a synchronization or coarse arithmetic anchor. The generating basis S
must remain distinct from the complete prime closure

    primeScalesUpTo A.

In general S is only a subset of that closure, not equal to it. The basis
inclusion proved below is the precise statement that each generating prime
direction is available in the complete world at the product anchor.

Once the complete closure primeScalesUpTo A is available, the existing
coarse-to-fine square certification proves every fine square world with
anchor q ≤ A. The product basis by itself is not claimed to certify the
square Body; the complete closure is essential. This bridge therefore has
the finite architecture

    S
      -> finitePrimeBasisProduct S = A
      -> primeScalesUpTo A
      -> every fine square world q ≤ A is certified.

The PCK-005 equality

    squarePrimeExpansion A = primeScalesUpTo (squareBody A)

is available from the Primitive layer, but this checkpoint adds no second
expansion operator and no optional specialization. No particular numeric
basis example is hard-coded here; that belongs to the next regression
checkpoint.

These results are finite support and order bridges only. They do not assert
that the basis equals its closure, do not define a new primorial, and make
no claim about unbounded prime generation, termination, Legendre, or
analytic consequences.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/--
Every member of a finite prime basis belongs to the canonical complete prime
world at the basis-product anchor.
-/
theorem finitePrimeBasis_subset_primeScalesUpTo_product
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) :
    S ⊆
      DkMath.NumberTheory.Primitive.primeScalesUpTo
        (finitePrimeBasisProduct S) := by
  intro p hp
  have hpPrime : Nat.Prime p := hS p hp
  have hpd : p ∣ finitePrimeBasisProduct S :=
    mem_dvd_finitePrimeBasisProduct hp
  have hproductPos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hpLe : p ≤ finitePrimeBasisProduct S :=
    Nat.le_of_dvd hproductPos hpd
  exact (mem_primeScalesUpTo).2 ⟨hpPrime, hpLe⟩

/--
The complete prime closure at a finite-basis product anchor certifies every
fine square world below that anchor.
-/
theorem prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody
    {S : Finset ℕ} {q m : ℕ}
    (hq : q ≤ finitePrimeBasisProduct S)
    (hm : 1 < m)
    (hmUpper :
      m ≤ DkMath.NumberTheory.Primitive.squareBody q)
    (hdisj :
      DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        (DkMath.NumberTheory.Primitive.primeScalesUpTo
          (finitePrimeBasisProduct S))
        m) :
    Nat.Prime m := by
  exact
    DkMath.NumberTheory.Primitive.prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
      hq hm hmUpper hdisj

end DkMath.NumberTheory.PrimorialUniverse
