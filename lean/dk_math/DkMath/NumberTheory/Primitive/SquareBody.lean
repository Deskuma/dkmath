/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.NumberTheory.Primitive.SquareBody"

/-!
## The natural-number square Body

This file records the generic arithmetic closure used by the Legendre entry
route.  It does not define a Legendre provider: it only says that a point
before the next square is prime when all prime directions up to the anchor
are absent.

The identity at the algebraic source layer is reused through
`CosmicFormulaBinom.cosmic_id_csr'`.  The order and primality arguments begin
only in the natural-number theorems below.
-/

namespace DkMath.NumberTheory.Primitive

open DkMath.CosmicFormulaBinom

/-- The unit-one square Body, written in its natural-number normal form. -/
def squareBody (P : ℕ) : ℕ := P ^ 2 + 2 * P

theorem unitSquare_body_eq (P : ℕ) :
    BodyN 2 P 1 = squareBody P := by
  simp only [BodyN]
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ, squareBody]
  ring

/-- The square Body ends immediately before the next consecutive square. -/
theorem squareBody_add_one_eq (P : ℕ) :
    squareBody P + 1 = (P + 1) ^ 2 := by
  simp [squareBody]
  ring

/--
Any composite point in the square Body has a prime divisor at most the
anchor.  This is the reusable arithmetic theorem; it does not mention
Legendre's conjecture or a finite prime set.
-/
theorem exists_prime_dvd_le_of_not_prime_of_le_squareBody
    {P m : ℕ} (hm : 1 < m) (hmUpper : m ≤ squareBody P)
    (hmPrime : ¬ Nat.Prime m) :
    ∃ q, Nat.Prime q ∧ q ∣ m ∧ q ≤ P := by
  have hminSq : m.minFac ^ 2 ≤ m :=
    Nat.minFac_sq_le_self (by omega : 0 < m) hmPrime
  have hltNext : m < (P + 1) ^ 2 := by
    calc
      m ≤ squareBody P := hmUpper
      _ < (P + 1) ^ 2 := by rw [← squareBody_add_one_eq P]; omega
  have hminLt : m.minFac < P + 1 := by
    nlinarith [hminSq, hltNext]
  refine ⟨m.minFac, Nat.minFac_prime (by omega : m ≠ 1),
    Nat.minFac_dvd m, ?_⟩
  omega

/--
Inside the square Body, excluding every prime direction up to `P` forces a
prime witness.
-/
theorem prime_of_supportDisjointFrom_le_squareBody
    {P m : ℕ} (hm : 1 < m) (hmUpper : m ≤ squareBody P)
    (hdisj : ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ P → ¬ q ∣ m) :
    Nat.Prime m := by
  by_contra hmPrime
  obtain ⟨q, hq, hqd, hqle⟩ :=
    exists_prime_dvd_le_of_not_prime_of_le_squareBody hm hmUpper hmPrime
  exact (hdisj hq hqle) hqd

end DkMath.NumberTheory.Primitive
