/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Finset.Interval
import DkMath.NumberTheory.Primitive.SquareBody

#print "file: DkMath.NumberTheory.Primitive.SquarePrimeExpansion"

/-!
## Finite square prime expansion

This module defines the first finite expansion operator for the canonical
prime world. It keeps the complete old support primeScalesUpTo P and adds
only the nontrivial points in the square Body window that escape every old
prime direction. The filter itself does not test primality; square-body
certification proves primality of the escaping points.

The resulting finite closure is exactly primeScalesUpTo (squareBody P).
This is a bounded equality of finite prime worlds, not an unbounded
prime-generation algorithm or a claim about computational efficiency.
-/

namespace DkMath.NumberTheory.Primitive

open DkMath.NumberTheory.StructuralArithmetic

/--
Extend the complete prime world at anchor P through its square Body.

The fresh part keeps the nontrivial points in the square window that escape
every old prime direction. It does not use Nat.Prime as a selection test.
-/
noncomputable def squarePrimeExpansion (P : ℕ) : Finset ℕ := by
  classical
  exact
    primeScalesUpTo P ∪
      (Finset.Icc 2 (squareBody P)).filter
        (fun n => SupportDisjointFrom (primeScalesUpTo P) n)

/--
Membership in the expansion is exactly primality below the square-Body
endpoint.
-/
theorem mem_squarePrimeExpansion_iff
    {P n : ℕ} :
    n ∈ squarePrimeExpansion P ↔
      Nat.Prime n ∧ n ≤ squareBody P := by
  classical
  constructor
  · intro hn
    rw [squarePrimeExpansion, Finset.mem_union] at hn
    rcases hn with hnOld | hnEscape
    · have hnPrime : Nat.Prime n := (mem_primeScalesUpTo.mp hnOld).1
      have hnLeP : n ≤ P := (mem_primeScalesUpTo.mp hnOld).2
      have hPLeBody : P ≤ squareBody P := by
        simpa [squareBody] using
          (show P ≤ P ^ 2 + 2 * P by nlinarith [Nat.zero_le P])
      exact ⟨hnPrime, hnLeP.trans hPLeBody⟩
    · rcases Finset.mem_filter.mp hnEscape with ⟨hnIcc, hdisj⟩
      have hnBounds : 2 ≤ n ∧ n ≤ squareBody P :=
        Finset.mem_Icc.mp hnIcc
      have hnPrime : Nat.Prime n :=
        prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
          (by omega) hnBounds.2 hdisj
      exact ⟨hnPrime, hnBounds.2⟩
  · rintro ⟨hnPrime, hnUpper⟩
    by_cases hnLeP : n ≤ P
    · exact Finset.mem_union_left _
        ((mem_primeScalesUpTo).2 ⟨hnPrime, hnLeP⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hnPrime.two_le, hnUpper⟩, ?_⟩
      intro r hr hrd hrMem
      have hrLeP : r ≤ P := (mem_primeScalesUpTo.mp hrMem).2
      have hrEqN : r = n :=
        (Nat.dvd_prime hnPrime).mp hrd |>.resolve_left hr.ne_one
      exact hnLeP (by simpa [hrEqN] using hrLeP)

/--
One finite square expansion reconstructs the canonical prime world through
the square-Body endpoint.
-/
theorem squarePrimeExpansion_eq_primeScalesUpTo_squareBody
    (P : ℕ) :
    squarePrimeExpansion P = primeScalesUpTo (squareBody P) := by
  ext n
  rw [mem_squarePrimeExpansion_iff, mem_primeScalesUpTo]

end DkMath.NumberTheory.Primitive
