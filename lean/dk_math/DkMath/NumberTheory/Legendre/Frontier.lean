/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Legendre.LocalizedObstruction
import DkMath.NumberTheory.Legendre.PacketUnitResidue
import DkMath.NumberTheory.Legendre.SmallCofactor

#print "file: DkMath.NumberTheory.Legendre.Frontier"

/-!
## Frontier

Final finite square-escape and Legendre equivalences, aggregating the current theorem layers.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-- Full cover is equivalent to equality of the covered and shell sets. -/
theorem squareOffsetsFullyCovered_iff_coveredSquareOffsets_eq
    {n : ℕ} :
    SquareOffsetsFullyCovered n ↔
      coveredSquareOffsets n = squareOffsets n := by
  constructor
  · intro hfull
    ext r
    constructor
    · intro hr
      exact mem_squareOffsets.mpr (mem_coveredSquareOffsets.mp hr).1
    · intro hr
      exact mem_coveredSquareOffsets.mpr ⟨mem_squareOffsets.mp hr, hfull r
        (mem_squareOffsets.mp hr)⟩
  · intro heq r hr
    have hmem : r ∈ coveredSquareOffsets n := by
      rw [heq]
      exact mem_squareOffsets.mpr hr
    exact (mem_coveredSquareOffsets.mp hmem).2

/-- Failure of full cover is equivalent to a nonempty escaping finite set. -/
theorem not_squareOffsetsFullyCovered_iff_escaping_nonempty
    {n : ℕ} :
    ¬ SquareOffsetsFullyCovered n ↔
      (escapingSquareOffsets n).Nonempty := by
  constructor
  · intro hnot
    classical
    by_contra hne
    apply hnot
    intro r hr
    by_contra hnotcovered
    apply hne
    exact ⟨r, mem_escapingSquareOffsets.mpr ⟨hr, hnotcovered⟩⟩
  · rintro ⟨r, hr⟩ hfull
    exact (mem_escapingSquareOffsets.mp hr).2 (hfull r
      (mem_escapingSquareOffsets.mp hr).1)

/-- The existing provider is exactly failure of complete finite square-wave cover. -/
theorem squareAnchoredSupportEscape_iff_not_fully_covered :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n → ¬ SquareOffsetsFullyCovered n := by
  constructor
  · intro hEscape n hn hfull
    obtain ⟨r, hr, hdisj⟩ := hEscape n hn
    exact (supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mp
      hdisj) (hfull r hr)
  · intro hCover n hn
    obtain ⟨r, hr⟩ :=
      (not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp (hCover n hn))
    have hmem := mem_escapingSquareOffsets.mp hr
    exact ⟨r, hmem.1,
      (supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hmem.2)⟩

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

/-- The Legendre conjecture is equivalently the finite square-offset escape frontier. -/
theorem legendreConjecture_iff_squareOffsets_not_fully_covered :
    LegendreConjecture ↔
      ∀ n : ℕ, 0 < n → ¬ SquareOffsetsFullyCovered n :=
  legendreConjecture_iff_squareAnchoredSupportEscape.trans
    squareAnchoredSupportEscape_iff_not_fully_covered

end DkMath.NumberTheory.Legendre
