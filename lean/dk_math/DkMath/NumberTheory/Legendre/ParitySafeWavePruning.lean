/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity

#print "file: DkMath.NumberTheory.Legendre.ParitySafeWavePruning"

/-!
## ParitySafeWavePruning

For each parity-safe active prime wave, retain its least candidate seat and
delete the remaining seats.  The resulting finite set is a canonical
support-disjoint provider: any active prime can occur in at most one retained
seat.  The construction is deliberately elementary and finite; it adds no
graph abstraction, prime-counting estimate, or universal lower bound.

The remaining arithmetic obligation is exposed as the single cardinal
inequality
`active.card + deletion.card < candidate.card`.  Under that inequality the
L034 capacity frontier returns a prime in the square cell.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ### PRIM-L035.1: active waves and canonical representatives -/

/-- Candidate seats hit by one active prime wave. -/
noncomputable def paritySafeActiveWaveOffsets (n q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorOddPointCoprimeOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n q r)

@[simp] theorem mem_paritySafeActiveWaveOffsets
    {n q r : ℕ} :
    r ∈ paritySafeActiveWaveOffsets n q ↔
      r ∈ squareAnchorOddPointCoprimeOffsets n ∧
        SquareOffsetForbiddenBy n q r := by
  simp [paritySafeActiveWaveOffsets]

@[simp] theorem mem_paritySafeActiveWaveOffsets_iff_dvd
    {n q r : ℕ} :
    r ∈ paritySafeActiveWaveOffsets n q ↔
      r ∈ squareAnchorOddPointCoprimeOffsets n ∧ q ∣ n ^ 2 + r := by
  simp [paritySafeActiveWaveOffsets, SquareOffsetForbiddenBy]

/-- The least hit of a wave, with a harmless default for an empty wave. -/
noncomputable def paritySafeActiveWaveRepresentative (n q : ℕ) : ℕ :=
  if hq : (paritySafeActiveWaveOffsets n q).Nonempty then
    (paritySafeActiveWaveOffsets n q).min' hq
  else 0

/-- All hits of a wave except its canonical representative. -/
noncomputable def paritySafeActiveWaveExtraOffsets (n q : ℕ) : Finset ℕ :=
  if hq : (paritySafeActiveWaveOffsets n q).Nonempty then
    (paritySafeActiveWaveOffsets n q).erase
      ((paritySafeActiveWaveOffsets n q).min' hq)
  else ∅

/-- Every extra seat came from the original wave. -/
theorem paritySafeActiveWaveExtraOffsets_subset
    (n q : ℕ) :
    paritySafeActiveWaveExtraOffsets n q ⊆ paritySafeActiveWaveOffsets n q := by
  classical
  unfold paritySafeActiveWaveExtraOffsets
  split
  · exact Finset.erase_subset _ _
  · simp

private theorem paritySafeActiveWaveExtraOffsets_card_le
    (n q : ℕ) :
    (paritySafeActiveWaveExtraOffsets n q).card ≤
      (paritySafeActiveWaveOffsets n q).card - 1 := by
  classical
  by_cases hq : (paritySafeActiveWaveOffsets n q).Nonempty
  · rw [paritySafeActiveWaveExtraOffsets, dif_pos hq]
    exact Finset.card_erase_of_mem (Finset.min'_mem _ hq) ▸ le_rfl
  · have hempty : paritySafeActiveWaveOffsets n q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hq
    simp [paritySafeActiveWaveExtraOffsets, hempty]

/-! ### PRIM-L035.2: global deletion and one-hit property -/

/-- The union of all active-wave extra seats. -/
noncomputable def paritySafeDuplicateDeletionSet (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).biUnion
    (fun q => paritySafeActiveWaveExtraOffsets n q)

/-- Candidate seats remaining after deleting all active-wave extras. -/
noncomputable def paritySafePrunedCandidates (n : ℕ) : Finset ℕ :=
  squareAnchorOddPointCoprimeOffsets n \ paritySafeDuplicateDeletionSet n

theorem paritySafeDuplicateDeletionSet_subset_candidate (n : ℕ) :
    paritySafeDuplicateDeletionSet n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  intro r hr
  rcases Finset.mem_biUnion.mp hr with ⟨q, hq, hqr⟩
  exact (mem_paritySafeActiveWaveOffsets.mp
    (paritySafeActiveWaveExtraOffsets_subset n q hqr)).1

theorem paritySafePrunedCandidates_subset_candidate (n : ℕ) :
    paritySafePrunedCandidates n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  intro r hr
  exact (Finset.mem_sdiff.mp hr).1

private theorem paritySafeWave_inter_pruned_subset_singleton
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    paritySafeActiveWaveOffsets n q ∩
        paritySafePrunedCandidates n ⊆
      {paritySafeActiveWaveRepresentative n q} := by
  classical
  intro r hr
  have hrwave := (Finset.mem_inter.mp hr).1
  have hrpruned := (Finset.mem_inter.mp hr).2
  by_cases hnonempty : (paritySafeActiveWaveOffsets n q).Nonempty
  · have hrep : paritySafeActiveWaveRepresentative n q =
        (paritySafeActiveWaveOffsets n q).min' hnonempty := by
      simp [paritySafeActiveWaveRepresentative, hnonempty]
    by_cases hre : r = paritySafeActiveWaveRepresentative n q
    · simp [hre]
    · have hre' : r ≠ (paritySafeActiveWaveOffsets n q).min' hnonempty := by
        simpa [hrep] using hre
      have hrExtra : r ∈ paritySafeActiveWaveExtraOffsets n q := by
        rw [paritySafeActiveWaveExtraOffsets, dif_pos hnonempty]
        exact Finset.mem_erase.mpr ⟨hre', hrwave⟩
      have hrDeletion : r ∈ paritySafeDuplicateDeletionSet n := by
        exact Finset.mem_biUnion.mpr ⟨q, hq, hrExtra⟩
      exact False.elim ((Finset.mem_sdiff.mp hrpruned).2 hrDeletion)
  · have hempty : paritySafeActiveWaveOffsets n q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hempty] at hrwave

/-- After global pruning, each active wave hits at most one retained seat. -/
theorem paritySafeActiveWave_inter_pruned_card_le_one
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    (paritySafeActiveWaveOffsets n q ∩
      paritySafePrunedCandidates n).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have hsubset := paritySafeWave_inter_pruned_subset_singleton hq
  have hr' := hsubset hr
  have hs' := hsubset hs
  exact (Finset.mem_singleton.mp hr').trans (Finset.mem_singleton.mp hs').symm

/-- The canonical pruned candidates have pairwise disjoint active supports. -/
theorem pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily_paritySafePrunedCandidates
    (n : ℕ) :
    PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n
      (paritySafePrunedCandidates n) := by
  classical
  refine ⟨paritySafePrunedCandidates_subset_candidate n, ?_⟩
  intro r hr s hs hrs
  change Disjoint (squareOffsetAnchorNondivisorSupport n r)
    (squareOffsetAnchorNondivisorSupport n s)
  rw [Finset.disjoint_left]
  intro q hqr hqs
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hqr
  have hcandidateR := (Finset.mem_sdiff.mp hr).1
  have hcandidateS := (Finset.mem_sdiff.mp hs).1
  have hoddR := (mem_squareAnchorOddPointCoprimeOffsets.mp hcandidateR).2
  have hqactive : q ∈ squareAnchorOddActivePrimes n := by
    have hqne : q ≠ 2 := by
      intro hq2
      subst q
      exact not_mem_squareOffsetAnchorNondivisorSupport_of_odd_point hoddR hqr
    exact mem_squareAnchorOddActivePrimes.mpr
      ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqne⟩
  have hmemr : r ∈ paritySafeActiveWaveOffsets n q :=
    mem_paritySafeActiveWaveOffsets.mpr ⟨hcandidateR, hq'.2.2.2⟩
  have hmems : s ∈ paritySafeActiveWaveOffsets n q := by
    have hqs' := mem_squareOffsetAnchorNondivisorSupport.mp hqs
    exact mem_paritySafeActiveWaveOffsets.mpr ⟨hcandidateS, hqs'.2.2.2⟩
  have hri : r ∈ paritySafeActiveWaveOffsets n q ∩
      paritySafePrunedCandidates n := Finset.mem_inter.mpr ⟨hmemr, hr⟩
  have hsi : s ∈ paritySafeActiveWaveOffsets n q ∩
      paritySafePrunedCandidates n := Finset.mem_inter.mpr ⟨hmems, hs⟩
  have hle := paritySafeActiveWave_inter_pruned_card_le_one hqactive
  exact hrs ((Finset.card_le_one.mp hle) r hri s hsi)

/-! ### PRIM-L035.4: deletion cardinality and frontier -/

/-- Deleting a finite subset gives the exact Nat-safe cardinal identity. -/
theorem paritySafePrunedCandidates_card_add_duplicateDeletionSet_card_eq_candidate_card
    (n : ℕ) :
    (paritySafePrunedCandidates n).card +
        (paritySafeDuplicateDeletionSet n).card =
      (squareAnchorOddPointCoprimeOffsets n).card := by
  rw [paritySafePrunedCandidates]
  rw [Finset.card_sdiff_add_card]
  rw [Finset.union_eq_left.mpr (paritySafeDuplicateDeletionSet_subset_candidate n)]

/-- The canonical active-wave provider reduces full cover to one cardinal target. -/
theorem exists_prime_squareCell_of_oddActivePrimes_card_add_duplicateDeletionSet_card_lt_candidate
    {n : ℕ} (hn : 0 < n)
    (hcard :
      (squareAnchorOddActivePrimes n).card +
          (paritySafeDuplicateDeletionSet n).card <
        (squareAnchorOddPointCoprimeOffsets n).card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have hpruned :
      (squareAnchorOddActivePrimes n).card <
        (paritySafePrunedCandidates n).card := by
    have hidentity :=
      paritySafePrunedCandidates_card_add_duplicateDeletionSet_card_eq_candidate_card n
    omega
  exact exists_prime_squareCell_of_oddActivePrimes_card_lt_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    hn (pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily_paritySafePrunedCandidates n)
    hpruned

/-! ### PRIM-L035.5: additive duplicate budget -/

/-- Sum of the local duplicate counts, with Nat subtraction local to each wave. -/
noncomputable def paritySafeWaveDuplicateBudget (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorOddActivePrimes n,
    ((paritySafeActiveWaveOffsets n q).card - 1)

/-- The union deletion cardinal is bounded by the additive duplicate budget. -/
theorem paritySafeDuplicateDeletionSet_card_le_waveDuplicateBudget
    (n : ℕ) :
    (paritySafeDuplicateDeletionSet n).card ≤
      paritySafeWaveDuplicateBudget n := by
  calc
    (paritySafeDuplicateDeletionSet n).card ≤
        ∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeActiveWaveExtraOffsets n q).card := by
      exact Finset.card_biUnion_le
    _ ≤ paritySafeWaveDuplicateBudget n := by
      apply Finset.sum_le_sum
      intro q hq
      exact paritySafeActiveWaveExtraOffsets_card_le n q

/-- The additive budget is a secondary sufficient frontier consumer. -/
theorem exists_prime_squareCell_of_oddActivePrimes_card_add_waveDuplicateBudget_lt_candidate
    {n : ℕ} (hn : 0 < n)
    (hcard :
      (squareAnchorOddActivePrimes n).card +
          paritySafeWaveDuplicateBudget n <
        (squareAnchorOddPointCoprimeOffsets n).card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_oddActivePrimes_card_add_duplicateDeletionSet_card_lt_candidate hn
  have hbudget := paritySafeDuplicateDeletionSet_card_le_waveDuplicateBudget n
  omega

end DkMath.NumberTheory.Legendre
