/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredPacketTriangle
import DkMath.NumberTheory.Legendre.Frontier

#print "file: DkMath.NumberTheory.Legendre.CoprimeSeatCapacity"

/-!
## CoprimeSeatCapacity

This module extracts the finite capacity principle behind the centered packet
examples.  A finite family of shell offsets with pairwise coprime complete
points has pairwise disjoint actual old-prime supports.  Under full cover each
support is nonempty, so the family cardinality cannot exceed the cardinality
of `primeScalesUpTo n`.

The strict reverse inequality is consumed locally by the Frontier API to
produce a prime in the square cell.  The module does not provide a universal
family with a growing cardinality and therefore does not prove Legendre's
conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L028.1: finite family predicate -/

/--
A finite family of actual square-shell seats whose complete points are
pairwise coprime.

The predicate deliberately records only shell membership and complete-point
coprimality; support nonemptiness is supplied separately by full cover.
-/
def PairwiseCoprimeSquareSeatFamily (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, SquareOffset n r) ∧
    ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      Nat.Coprime (n ^ 2 + r) (n ^ 2 + s)

/-! ### PRIM-L028.2: support containment -/

/-- Every actual seat support is contained in the bounded old-prime world. -/
theorem squareOffsetPrimeSupport_subset_primeScalesUpTo
    {n r : ℕ} :
    squareOffsetPrimeSupport n r ⊆ primeScalesUpTo n := by
  intro q hq
  exact mem_primeScalesUpTo.mpr
    ⟨(mem_squareOffsetPrimeSupport.mp hq).1,
      (mem_squareOffsetPrimeSupport.mp hq).2.1⟩

/-! ### PRIM-L028.3: pairwise support disjointness -/

/-- Distinct members of a coprime seat family have disjoint actual supports. -/
theorem pairwiseDisjoint_squareOffsetPrimeSupport_of_family
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseCoprimeSquareSeatFamily n R) :
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetPrimeSupport n r) := by
  intro r hr s hs hrs
  exact disjoint_squareOffsetPrimeSupport_of_coprime_points
    (hfamily.2 r hr s hs hrs)

/-! ### PRIM-L028.4: full-cover support nonemptiness -/

/-- Full cover makes every seat support in a finite family nonempty. -/
theorem squareOffsetPrimeSupport_nonempty_of_family_fullyCovered
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseCoprimeSquareSeatFamily n R)
    (hfull : SquareOffsetsFullyCovered n) :
    ∀ r ∈ R, (squareOffsetPrimeSupport n r).Nonempty := by
  intro r hr
  apply squareOffsetCovered_iff_primeSupport_nonempty.mp
  exact hfull r (hfamily.1 r hr)

/-! ### PRIM-L028.5: finite capacity -/

/--
Full cover bounds the number of pairwise-coprime actual seats by the number
of available bounded old-prime directions.

The proof counts the finite union of actual supports.  Pairwise disjointness
turns its cardinality into the sum of support cardinalities, full cover makes
each summand positive, and support containment places the union inside
`primeScalesUpTo n`.
-/
theorem card_pairwiseCoprimeSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseCoprimeSquareSeatFamily n R)
    (hfull : SquareOffsetsFullyCovered n) :
    R.card ≤ (primeScalesUpTo n).card := by
  classical
  have hdisj := pairwiseDisjoint_squareOffsetPrimeSupport_of_family hfamily
  have hnonempty := squareOffsetPrimeSupport_nonempty_of_family_fullyCovered
    hfamily hfull
  have hunion :
      R.biUnion (fun r => squareOffsetPrimeSupport n r) ⊆
        primeScalesUpTo n := by
    intro q hq
    simp only [Finset.mem_biUnion] at hq
    rcases hq with ⟨r, hr, hqr⟩
    exact squareOffsetPrimeSupport_subset_primeScalesUpTo hqr
  calc
    R.card = ∑ r ∈ R, 1 := by simp
    _ ≤ ∑ r ∈ R, (squareOffsetPrimeSupport n r).card := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.card_pos.mpr (hnonempty r hr)
    _ = (R.biUnion (fun r => squareOffsetPrimeSupport n r)).card := by
      symm
      exact Finset.card_biUnion hdisj
    _ ≤ (primeScalesUpTo n).card := Finset.card_le_card hunion

/-! ### PRIM-L028.6: direct capacity obstruction -/

/-- A seat family larger than the old-prime world prevents full cover. -/
theorem not_fullyCovered_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseCoprimeSquareSeatFamily n R)
    (hcard : (primeScalesUpTo n).card < R.card) :
    ¬ SquareOffsetsFullyCovered n := by
  intro hfull
  exact (not_le_of_gt hcard)
    (card_pairwiseCoprimeSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
      hfamily hfull)

/-! ### PRIM-L028.7: local prime-square-cell consumer -/

/--
A strict finite capacity violation yields an actual prime in the square cell.

This is local in `n`: it consumes the existing finite Frontier theorem and
does not assert a universal family or Legendre's conjecture.
-/
theorem exists_prime_squareCell_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
    {n : ℕ} {R : Finset ℕ}
    (hn : 0 < n)
    (hfamily : PairwiseCoprimeSquareSeatFamily n R)
    (hcard : (primeScalesUpTo n).card < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have hnotfull :=
    not_fullyCovered_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
      hfamily hcard
  obtain ⟨r, hr⟩ :=
    not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp hnotfull
  have hescape := mem_escapingSquareOffsets.mp hr
  have hdisj :
      SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) :=
    supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr
      hescape.2
  refine ⟨n ^ 2 + r,
    prime_of_squareAnchoredSupportEscape hn hescape.1 hdisj, ?_⟩
  exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr
    ⟨r, hescape.1, rfl⟩

end DkMath.NumberTheory.Legendre
