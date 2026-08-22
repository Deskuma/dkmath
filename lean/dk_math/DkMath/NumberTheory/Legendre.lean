/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import DkMath.NumberTheory.Primitive.SquareBody

#print "file: DkMath.NumberTheory.Legendre"

/-!
## Legendre's conjecture as a square-anchored support escape

The formalization in this file separates the proved arithmetic framework from
the unresolved provider.  A support-free point in the open interval between
two consecutive squares is prime by the generic square-Body theorem.  The
universal existence of such a point is recorded explicitly as
`SquareAnchoredSupportEscape`; it is the Legendre-equivalent frontier and is
not assumed here.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- The open interval between the consecutive squares anchored at `n`. -/
def SquareCell (n m : ℕ) : Prop :=
  n ^ 2 < m ∧ m < (n + 1) ^ 2

/-- The offset coordinates of a point in a consecutive-square cell. -/
def SquareOffset (n r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ 2 * n

/-- Exact conversion between square-cell and square-offset coordinates. -/
theorem squareCell_iff_exists_squareOffset (n m : ℕ) :
    SquareCell n m ↔
      ∃ r, SquareOffset n r ∧ m = n ^ 2 + r := by
  have hsquare : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
    ring
  constructor
  · intro hcell
    dsimp [SquareCell] at hcell
    rcases hcell with ⟨hlo, hhi⟩
    have hbase : n ^ 2 ≤ m := by omega
    refine ⟨m - n ^ 2, ?_, ?_⟩
    · dsimp [SquareOffset]
      constructor <;> omega
    · rw [hsquare] at hhi
      omega
  · rintro ⟨r, hr, rfl⟩
    dsimp [SquareCell, SquareOffset] at hr ⊢
    rw [hsquare]
    omega

/--
The usual Legendre statement: every positive square interval contains a prime.
-/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ p, Nat.Prime p ∧ SquareCell n p

/--
The local provider form: an offset in every square cell avoids all prime
directions at most the anchor.
-/
def SquareAnchoredSupportEscape : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ r, SquareOffset n r ∧
      SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r)

/--
The semantic square-escape provider expanded into its elementary bounded-prime
form.  This is a rewrite theorem, not an existence theorem.
-/
theorem squareAnchoredSupportEscape_iff_raw :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n →
        ∃ r, SquareOffset n r ∧
          ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ n → ¬ q ∣ n ^ 2 + r := by
  constructor
  · intro hEscape n hn
    obtain ⟨r, hr, hdisj⟩ := hEscape n hn
    exact ⟨r, hr, supportDisjointFrom_primeScalesUpTo_iff.mp hdisj⟩
  · intro hRaw n hn
    obtain ⟨r, hr, hdisj⟩ := hRaw n hn
    exact ⟨r, hr, supportDisjointFrom_primeScalesUpTo_iff.mpr hdisj⟩

/-- A support-free offset produces a prime point in its square cell. -/
theorem prime_of_squareAnchoredSupportEscape
    {n r : ℕ} (hn : 0 < n) (hr : SquareOffset n r)
    (hdisj : SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r)) :
    Nat.Prime (n ^ 2 + r) := by
  have hnSq : 1 ≤ n ^ 2 := by nlinarith
  have hm : 1 < n ^ 2 + r := by
    dsimp [SquareOffset] at hr
    omega
  have hmUpper : n ^ 2 + r ≤ squareBody n := by
    dsimp [SquareOffset] at hr
    dsimp [squareBody]
    omega
  exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody hm hmUpper hdisj

/-- The support-escape provider gives the usual Legendre witness. -/
theorem legendreConjecture_of_squareAnchoredSupportEscape
    (hEscape : SquareAnchoredSupportEscape) :
    LegendreConjecture := by
  intro n hn
  obtain ⟨r, hr, hdisj⟩ := hEscape n hn
  refine ⟨n ^ 2 + r, prime_of_squareAnchoredSupportEscape hn hr hdisj, ?_⟩
  exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).2 ⟨r, hr, rfl⟩

/--
The usual conjecture is exactly the square-anchored support-escape provider.

The reverse implication uses only the fact that a prime divisor of a prime is
the prime itself, together with `q ≤ n < p` inside the square cell.  Thus this
theorem is a reduction, not a proof of the provider.
-/
theorem legendreConjecture_iff_squareAnchoredSupportEscape :
    LegendreConjecture ↔ SquareAnchoredSupportEscape := by
  constructor
  · intro hLegendre n hn
    obtain ⟨p, hp, hcell⟩ := hLegendre n hn
    obtain ⟨r, hr, hrEq⟩ :=
      (squareCell_iff_exists_squareOffset n p).1 hcell
    refine ⟨r, hr, ?_⟩
    apply supportDisjointFrom_primeScalesUpTo_iff.mpr
    intro q hq hqle hqdiv
    have hqdiv' : q ∣ p := by simpa [hrEq] using hqdiv
    have hqp : q = p :=
      ((Nat.dvd_prime hp).mp hqdiv').resolve_left hq.ne_one
    have hpLower : n ^ 2 < p := by
      rw [hrEq]
      dsimp [SquareOffset] at hr
      omega
    have hnSq : n ≤ n ^ 2 := by nlinarith
    rw [hqp] at hqle
    omega
  · exact legendreConjecture_of_squareAnchoredSupportEscape

end DkMath.NumberTheory.Legendre
