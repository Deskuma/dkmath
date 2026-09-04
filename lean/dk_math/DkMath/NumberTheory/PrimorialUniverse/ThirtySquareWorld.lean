/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge

#print "file: DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld"

/-!
## The canonical thirty-world square regression

This module records the concrete two-stage closure

    {2, 3, 5}
      -> 30
      -> primeScalesUpTo 30
      -> primeScalesUpTo 960.

The first arrow is product synchronization by the finite prime basis
product. The second arrow is completion of prime support, not wheel
survival. The third arrow is the finite square expansion from PCK-005.

The generating basis {2, 3, 5} is not the complete prime support through 30:
the complete closure also contains 7, 11, 13, 17, 19, 23, and 29. The
complete support primeScalesUpTo 30, rather than the basis alone, certifies
every fine square world with anchor q ≤ 30.

The endpoint is

    squareBody 30 = 960 = 31^2 - 1.

This is a finite regression only. It does not assert Legendre, one prime per
square interval, wheel survivors are prime, or unbounded prime generation.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- The canonical basis {2, 3, 5} is contained in the complete closure at 30. -/
theorem primeBasis235_subset_primeScalesUpTo_thirty :
    ({2, 3, 5} : Finset ℕ) ⊆
      DkMath.NumberTheory.Primitive.primeScalesUpTo 30 := by
  have h235 : IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  simpa only [finitePrimeBasisProduct_two_three_five] using
    (finitePrimeBasis_subset_primeScalesUpTo_product h235)

/-- The complete prime closure through 30, written explicitly. -/
theorem primeScalesUpTo_thirty_eq :
    DkMath.NumberTheory.Primitive.primeScalesUpTo 30 =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  decide

/-- The square Body at the canonical product anchor is 960. -/
@[simp]
theorem squareBody_thirty :
    DkMath.NumberTheory.Primitive.squareBody 30 = 960 := by
  norm_num [DkMath.NumberTheory.Primitive.squareBody]

/-- The same endpoint is one less than the next square, 31 squared. -/
theorem squareBody_thirty_add_one_eq_thirtyOne_sq :
    DkMath.NumberTheory.Primitive.squareBody 30 + 1 = 31 ^ 2 := by
  rw [squareBody_thirty]
  norm_num

/-- PCK-005 expands the complete thirty-world support through 960. -/
theorem squarePrimeExpansion_thirty_eq_primeScalesUpTo_960 :
    DkMath.NumberTheory.Primitive.squarePrimeExpansion 30 =
      DkMath.NumberTheory.Primitive.primeScalesUpTo 960 := by
  calc
    DkMath.NumberTheory.Primitive.squarePrimeExpansion 30 =
        DkMath.NumberTheory.Primitive.primeScalesUpTo
          (DkMath.NumberTheory.Primitive.squareBody 30) :=
      DkMath.NumberTheory.Primitive.squarePrimeExpansion_eq_primeScalesUpTo_squareBody 30
    _ = DkMath.NumberTheory.Primitive.primeScalesUpTo 960 := by
      rw [squareBody_thirty]

/--
The complete thirty-world support certifies every fine square world with
anchor q ≤ 30.
-/
theorem prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody
    {q m : ℕ}
    (hq : q ≤ 30)
    (hm : 1 < m)
    (hmUpper :
      m ≤ DkMath.NumberTheory.Primitive.squareBody q)
    (hdisj :
      DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        (DkMath.NumberTheory.Primitive.primeScalesUpTo 30) m) :
    Nat.Prime m := by
  exact
    prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody
      (S := ({2, 3, 5} : Finset ℕ)) (q := q) (m := m)
      (by simpa only [finitePrimeBasisProduct_two_three_five] using hq)
      hm hmUpper
      (by simpa only [finitePrimeBasisProduct_two_three_five] using hdisj)

/-- Representative square boundaries below and at the canonical anchor. -/
theorem representative_fine_square_boundaries_under_thirty :
    DkMath.NumberTheory.Primitive.squareBody 6 + 1 = 7 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 10 + 1 = 11 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 12 + 1 = 13 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 16 + 1 = 17 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 18 + 1 = 19 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 22 + 1 = 23 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 28 + 1 = 29 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 30 + 1 = 31 ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      DkMath.NumberTheory.Primitive.squareBody 6 + 1 = (6 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 6
      _ = 7 ^ 2 := by norm_num
  · calc
      DkMath.NumberTheory.Primitive.squareBody 10 + 1 = (10 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 10
      _ = 11 ^ 2 := by norm_num
  · calc
      DkMath.NumberTheory.Primitive.squareBody 12 + 1 = (12 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 12
      _ = 13 ^ 2 := by norm_num
  · calc
      DkMath.NumberTheory.Primitive.squareBody 16 + 1 = (16 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 16
      _ = 17 ^ 2 := by norm_num
  · calc
      DkMath.NumberTheory.Primitive.squareBody 18 + 1 = (18 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 18
      _ = 19 ^ 2 := by norm_num
  · calc
      DkMath.NumberTheory.Primitive.squareBody 22 + 1 = (22 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 22
      _ = 23 ^ 2 := by norm_num
  · calc
      DkMath.NumberTheory.Primitive.squareBody 28 + 1 = (28 + 1) ^ 2 :=
        DkMath.NumberTheory.Primitive.squareBody_add_one_eq 28
      _ = 29 ^ 2 := by norm_num
  · exact squareBody_thirty_add_one_eq_thirtyOne_sq

/--
49 survives the generating basis but fails against the complete closure and
is not prime. This blocks confusing basis survival with primality.
-/
theorem fortyNine_basis_vs_completeClosure_firewall :
    DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        ({2, 3, 5} : Finset ℕ) 49 ∧
    ¬ DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        (DkMath.NumberTheory.Primitive.primeScalesUpTo 30) 49 ∧
    ¬ Nat.Prime 49 := by
  constructor
  · intro q hq hq49
    have hqprod : q ∣ 7 * 7 := by
      simpa using hq49
    have hq7 : q ∣ 7 := by
      rcases hq.dvd_mul.mp hqprod with h | h <;> exact h
    have hqeq : q = 7 :=
      (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7 |>.resolve_left hq.ne_one
    simp [hqeq]
  constructor
  · intro hdisj
    have h7notmem : 7 ∉
        DkMath.NumberTheory.Primitive.primeScalesUpTo 30 :=
      hdisj (by norm_num : Nat.Prime 7) (by norm_num : 7 ∣ 49)
    exact h7notmem ((mem_primeScalesUpTo).2 ⟨by norm_num, by norm_num⟩)
  · norm_num

end DkMath.NumberTheory.PrimorialUniverse
