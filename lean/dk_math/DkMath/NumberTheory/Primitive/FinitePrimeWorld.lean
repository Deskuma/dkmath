/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection

#print "file: DkMath.NumberTheory.Primitive.FinitePrimeWorld"

/-!
## Canonical finite prime worlds

`primeScalesUpTo P` is the finite world containing precisely the prime
directions not exceeding `P`.  This module connects that concrete finite set
to the semantic `SupportDisjointFrom` predicate.  It does not define a sieve
period, a primorial, or any Legendre provider.
-/

namespace DkMath.NumberTheory.Primitive

open DkMath.NumberTheory.StructuralArithmetic

/-- The finite set of all prime directions at most `P`. -/
def primeScalesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter Nat.Prime

/-- Membership in `primeScalesUpTo P` is exactly bounded primality. -/
@[simp] theorem mem_primeScalesUpTo {P q : ℕ} :
    q ∈ primeScalesUpTo P ↔ Nat.Prime q ∧ q ≤ P := by
  simp [primeScalesUpTo, Nat.lt_succ_iff, and_comm]

/-- The canonical bounded world is certified to contain only primes. -/
theorem knownPrimeScales_primeScalesUpTo (P : ℕ) :
    KnownPrimeScales (primeScalesUpTo P) := by
  intro q hq
  exact (mem_primeScalesUpTo.mp hq).1

/--
Support disjointness from the canonical bounded world is the raw bounded-prime
divisibility condition used by the square-Body and Legendre layers.
-/
theorem supportDisjointFrom_primeScalesUpTo_iff
    {P m : ℕ} :
    SupportDisjointFrom (primeScalesUpTo P) m ↔
      ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ P → ¬ q ∣ m := by
  constructor
  · intro hdisj q hq hqle hqd
    exact hdisj hq hqd ((mem_primeScalesUpTo).2 ⟨hq, hqle⟩)
  · intro hraw q hq hqd hqmem
    have hqle := (mem_primeScalesUpTo.mp hqmem).2
    exact hraw hq hqle hqd

end DkMath.NumberTheory.Primitive
