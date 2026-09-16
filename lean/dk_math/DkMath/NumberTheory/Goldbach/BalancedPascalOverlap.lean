/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.Goldbach.BalancedCapacity
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedPascalOverlap"

/-!
# Balanced-window Pascal overlap

This module adds only the pair and triple layers needed to obtain a safe lower
bound for first-overlap excess.  It is a finite combinatorial ledger and does
not assert a universal survivor provider.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive

open scoped BigOperators

/-- The pure local Pascal inequality behind the pair-minus-triple bound. -/
theorem choose_two_le_sub_one_add_choose_three (k : ℕ) :
    Nat.choose k 2 ≤ (k - 1) + Nat.choose k 3 := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_succ_succ, Nat.choose_succ_succ]
      simp [Nat.choose_succ_succ]
      omega

/-- Pair obstruction multiplicity at one window seat. -/
def goldbachWindowLocalPairMultiplicity
    (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupportIn n t S).card 2

/-- Triple obstruction multiplicity at one window seat. -/
def goldbachWindowLocalTripleMultiplicity
    (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupportIn n t S).card 3

/-- Pair multiplicity summed over the balanced window. -/
def goldbachWindowPairOverlapCount (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalPairMultiplicity n w S t

/-- Triple multiplicity summed over the balanced window. -/
def goldbachWindowTripleOverlapCount (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalTripleMultiplicity n w S t

/-- Seat-local pair multiplicity is paid by first overlap plus triples. -/
theorem goldbachWindowLocalPairMultiplicity_le_overlap_add_triple
    (n w : ℕ) (S : Finset ℕ) (t : ℕ) :
    goldbachWindowLocalPairMultiplicity n w S t ≤
      goldbachWindowLocalOverlapExcess n w S t +
        goldbachWindowLocalTripleMultiplicity n w S t := by
  unfold goldbachWindowLocalPairMultiplicity
    goldbachWindowLocalOverlapExcess goldbachWindowLocalTripleMultiplicity
  exact choose_two_le_sub_one_add_choose_three _

/-- Window pair multiplicity is bounded by overlap excess plus triple mass. -/
theorem goldbachWindowPairOverlapCount_le_overlap_add_triple
    (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowPairOverlapCount n w S ≤
      goldbachWindowOverlapExcess n w S +
        goldbachWindowTripleOverlapCount n w S := by
  unfold goldbachWindowPairOverlapCount goldbachWindowOverlapExcess
    goldbachWindowTripleOverlapCount
  simpa [Finset.sum_add_distrib] using
    (Finset.sum_le_sum
      (fun t ht => goldbachWindowLocalPairMultiplicity_le_overlap_add_triple
        n w S t))

/-- Pair-minus-triple is a safe lower bound for first-overlap excess. -/
theorem goldbachWindowPairOverlap_sub_triple_le_overlap
    (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowPairOverlapCount n w S -
        goldbachWindowTripleOverlapCount n w S ≤
      goldbachWindowOverlapExcess n w S := by
  have h := goldbachWindowPairOverlapCount_le_overlap_add_triple n w S
  omega

/-- The Pascal pair-minus-triple budget supplies a generic window survivor. -/
theorem goldbachWindowSurvivor_of_incidence_le_of_pairMinusTriple_budget
    {n w : ℕ} {S : Finset ℕ} {C : ℕ}
    (hincidence : goldbachWindowIncidence n w S ≤ C)
    (hbudget : C <
      (goldbachBalancedOffsets n w).card +
        (goldbachWindowPairOverlapCount n w S -
          goldbachWindowTripleOverlapCount n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_incidence_le_of_overlap_le hincidence
    (e := goldbachWindowPairOverlapCount n w S -
      goldbachWindowTripleOverlapCount n w S)
  · exact goldbachWindowPairOverlap_sub_triple_le_overlap n w S
  · exact hbudget

/-- Width-local residue capacity plus Pascal payment supplies a survivor. -/
theorem goldbachWindowSurvivor_of_residue_capacity_of_pairMinusTriple_budget
    {n w : ℕ} {S : Finset ℕ}
    (hbudget :
      (∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1)) <
        (goldbachBalancedOffsets n w).card +
          (goldbachWindowPairOverlapCount n w S -
            goldbachWindowTripleOverlapCount n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_incidence_le_of_pairMinusTriple_budget
    (C := ∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1))
  · exact goldbachWindow_incidence_le_residue_capacity n w S
  · exact hbudget

/-- Anchor-local conditional Goldbach closure from the Pascal payment. -/
theorem goldbachPairAt_of_goldbachWindow_residue_capacity_of_pairMinusTriple_budget
    {n w P : ℕ}
    (hw : w ≤ n)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hbudget :
      (∑ r ∈ primeScalesUpTo P,
        (if r ∣ 2 * n then 1 else 2) * (w / r + 1)) <
        (goldbachBalancedOffsets n w).card +
          (goldbachWindowPairOverlapCount n w (primeScalesUpTo P) -
            goldbachWindowTripleOverlapCount n w (primeScalesUpTo P))) :
    GoldbachPairAt n := by
  have hsurvivor :=
    goldbachWindowSurvivor_of_residue_capacity_of_pairMinusTriple_budget
      (S := primeScalesUpTo P) hbudget
  obtain ⟨t, ht⟩ := hsurvivor
  exact goldbachPairAt_of_goldbachWindowSurvivor hw
    (mem_goldbachWindowSurvivors.mp ht).1 hanchor hhorizon
    (mem_goldbachWindowSurvivors.mp ht).2

end DkMath.NumberTheory
