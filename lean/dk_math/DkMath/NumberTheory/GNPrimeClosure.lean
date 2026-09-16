/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.NumberTheory.GNPrimeClosure"

namespace DkMath.NumberTheory

/-!
## Prime closure for the canonical GN factorization

The theorems in this file are the elementary factor-one layer for the
canonical product `x * GN d x u`.  They do not assert that `GN d x u` is
prime; they only expose what follows when the product, or the GN kernel,
is known to be prime.
-/

open DkMath.CosmicFormulaBinom

/--
The prime product `x * GN d x u` has exactly one of two factor-one channels:
the boundary channel `x = 1` with prime GN kernel, or the GN kernel channel
`GN d x u = 1` with prime boundary.  In particular, this symmetric theorem
keeps the genuine degenerate case `d = 1`, where the GN kernel can be `1`.
-/
theorem prime_boundary_mul_GN_iff
    {d x u : ℕ} :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔
      (x = 1 ∧ Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) ∨
      (DkMath.CosmicFormulaBinom.GN d x u = 1 ∧ Nat.Prime x) := by
  simp [Nat.prime_mul_iff, and_comm, or_comm]

/--
If the GN kernel itself is prime, then the canonical product is prime exactly
through the boundary channel `x = 1`.  This is the one-way GN-prime
specialization of `prime_boundary_mul_GN_iff`; it does not claim that GN is
prime without the explicit hypothesis `hGN`.
-/
theorem prime_boundary_mul_GN_iff_boundary_eq_one_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔ x = 1 := by
  constructor
  · intro hProduct
    rcases (prime_boundary_mul_GN_iff (d := d) (x := x) (u := u)).mp hProduct with
      ⟨hx, _⟩ | ⟨hGNOne, _⟩
    · exact hx
    · exact (hGN.ne_one hGNOne).elim
  · intro hx
    simpa [hx] using hGN

end DkMath.NumberTheory
