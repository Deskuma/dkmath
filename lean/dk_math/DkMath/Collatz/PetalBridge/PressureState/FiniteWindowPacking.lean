/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureState

#print "file: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking"

namespace DkMath.Collatz

/-!
# Finite-window pressure packing

This module is the first progressive extraction from `PressureState.lean`.
The established carrier API remains in that module for compatibility; new
packing-density results live here.  A later mechanical checkpoint may move the
stable carrier declarations here after splitting the state file into a core
module, without changing theorem names.
-/

/-- Equal pair keys determine equal packing units by proof irrelevance. -/
theorem SourcePressureFiniteWindowPackingUnit.eq_of_pairKey_eq
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
    (hkey : u₁.pairKey = u₂.pairKey) :
    u₁ = u₂ := by
  cases u₁
  cases u₂
  simp_all [SourcePressureFiniteWindowPackingUnit.pairKey]

/-- Distinct packing units have distinct oriented endpoint keys. -/
theorem SourcePressureFiniteWindowPackingUnit.pairKey_ne_of_ne
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
    (hne : u₁ ≠ u₂) :
    u₁.pairKey ≠ u₂.pairKey :=
  fun hkey => hne (SourcePressureFiniteWindowPackingUnit.eq_of_pairKey_eq hkey)

/--
Distinct canonical separators in a sorted witness list are separated by at
least two positions.

Sorted adjacency puts one oriented pair wholly before the other.  The
two-center spacing inside the earlier unit then leaves two steps between the
canonical left-next separators.
-/
theorem SourcePressureFiniteWindowPackingUnit.canonicalSeparator_two_separated_of_ne_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
    (hne : u₁ ≠ u₂) :
    u₁.canonicalSeparator + 2 ≤ u₂.canonicalSeparator ∨
      u₂.canonicalSeparator + 2 ≤ u₁.canonicalSeparator := by
  rcases sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
      hsorted u₁.state.adjacentPair u₂.state.adjacentPair with hpairs | horder
  · exfalso
    apply hne
    cases u₁
    cases u₂
    simp_all
  · rcases horder with h₁₂ | h₂₁
    · left
      have hgap := u₁.state.finiteWindow.two_le_value_gap
      simp only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator]
      omega
    · right
      have hgap := u₂.state.finiteWindow.two_le_value_gap
      simp only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator]
      omega

/--
Generic finite-window packing bound for natural numbers separated by two.

The map `m ↦ (m - lo) / 2` is injective on a two-separated set and its image
lies in `range ((hi - lo) / 2 + 1)`.
-/
theorem finset_card_le_half_window_add_one_of_twoSeparated
    {lo hi : ℕ}
    (T : Finset ℕ)
    (hwindow : ∀ m ∈ T, lo ≤ m ∧ m ≤ hi)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a < b → a + 2 ≤ b) :
    T.card ≤ (hi - lo) / 2 + 1 := by
  classical
  let f : ℕ → ℕ := fun m => (m - lo) / 2
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hablt | hbalt
    · have hgap := hsep a ha b hb hablt
      have hawa := hwindow a ha
      simp only [f] at hab
      omega
    · have hgap := hsep b hb a ha hbalt
      have hawb := hwindow b hb
      simp only [f] at hab
      omega
  have hcard : (T.image f).card = T.card :=
    Finset.card_image_iff.mpr hinj
  have hsubset : T.image f ⊆ Finset.range ((hi - lo) / 2 + 1) := by
    intro q hq
    rcases Finset.mem_image.1 hq with ⟨m, hm, rfl⟩
    have hwm := hwindow m hm
    simp only [Finset.mem_range, f]
    omega
  rw [← hcard]
  simpa using Finset.card_le_card hsubset

/-- Nonpositive pressure-margin coordinates in the explicit finite window. -/
noncomputable def sourcePressureNonposPositionsInWindow
    (n : OddNat) (k lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter
    (fun m => SourcePressureMarginInt n k m ≤ 0)

@[simp]
theorem mem_sourcePressureNonposPositionsInWindow
    {n : OddNat} {k lo hi m : ℕ} :
    m ∈ sourcePressureNonposPositionsInWindow n k lo hi ↔
      lo ≤ m ∧ m ≤ hi ∧ SourcePressureMarginInt n k m ≤ 0 := by
  simp [sourcePressureNonposPositionsInWindow, and_assoc]

/-- Canonical separators of a finite family are nonpositive window positions. -/
theorem sourcePressureFiniteWindowPackingUnit_image_separator_subset_nonposPositions
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
    S.image (SourcePressureFiniteWindowPackingUnit.canonicalSeparator
      (L := L) (lo := lo) (hi := hi)) ⊆
      sourcePressureNonposPositionsInWindow n k lo hi := by
  classical
  intro m hm
  rcases Finset.mem_image.1 hm with ⟨u, _hu, rfl⟩
  rcases u.canonicalSeparator_in_window with ⟨hlo, hhi⟩
  exact mem_sourcePressureNonposPositionsInWindow.2
    ⟨hlo, hhi, u.state.separator_nonpos⟩

/--
Sign-restricted packing bound: canonical units inject into the nonpositive
pressure positions of the same finite window.
-/
theorem sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
    S.card ≤ (sourcePressureNonposPositionsInWindow n k lo hi).card := by
  classical
  let f := SourcePressureFiniteWindowPackingUnit.canonicalSeparator
    (L := L) (lo := lo) (hi := hi)
  have hinj : Function.Injective f :=
    SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
      hsorted
  have hcard : (S.image f).card = S.card :=
    Finset.card_image_iff.mpr hinj.injOn
  rw [← hcard]
  exact Finset.card_le_card
    (sourcePressureFiniteWindowPackingUnit_image_separator_subset_nonposPositions S)

/--
Sharp finite-window pressure packing bound from canonical-separator
two-spacing.
-/
theorem sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
    S.card ≤ (hi - lo) / 2 + 1 := by
  classical
  let f := SourcePressureFiniteWindowPackingUnit.canonicalSeparator
    (L := L) (lo := lo) (hi := hi)
  have hinj : Function.Injective f :=
    SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
      hsorted
  have hcard : (S.image f).card = S.card :=
    Finset.card_image_iff.mpr hinj.injOn
  have hwindow : ∀ m ∈ S.image f, lo ≤ m ∧ m ≤ hi := by
    intro m hm
    rcases Finset.mem_image.1 hm with ⟨u, _hu, rfl⟩
    exact u.canonicalSeparator_in_window
  have hsep :
      ∀ a ∈ S.image f, ∀ b ∈ S.image f, a < b → a + 2 ≤ b := by
    intro a ha b hb hab
    rcases Finset.mem_image.1 ha with ⟨u₁, hu₁, rfl⟩
    rcases Finset.mem_image.1 hb with ⟨u₂, hu₂, hsepEq⟩
    subst b
    have hne : u₁ ≠ u₂ := by
      intro hu
      subst u₂
      omega
    rcases u₁.canonicalSeparator_two_separated_of_ne_of_sorted hsorted hne with
      hforward | hreverse
    · simpa only [f] using hforward
    · simp only [f] at hab hreverse
      omega
  rw [← hcard]
  exact finset_card_le_half_window_add_one_of_twoSeparated
    (S.image f) hwindow hsep

/--
Finite local-Big packing surface: geometry supplies half-window capacity while
pressure signs supply the nonpositive-position capacity.
-/
theorem sourcePressureFiniteWindowPackingUnit_localBig
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
    S.card ≤ (hi - lo) / 2 + 1 ∧
      S.card ≤ (sourcePressureNonposPositionsInWindow n k lo hi).card :=
  ⟨sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one hsorted S,
    sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions hsorted S⟩

/--
Canonical oriented-pair family extracted directly from adjacent entries of `L`.

The zip with `L.tail` enumerates adjacent pair keys; the filter retains exactly
those carrying the canonical finite-window packing state.
-/
noncomputable def sourcePressureCanonicalPackingPairFamily
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) :
    Finset (SourcePressureLocalIslandWitness n k r ×
      SourcePressureLocalIslandWitness n k r) := by
  classical
  exact (L.zip L.tail).toFinset.filter fun P =>
    SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2

@[simp]
theorem mem_sourcePressureCanonicalPackingPairFamily
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    {P : SourcePressureLocalIslandWitness n k r ×
      SourcePressureLocalIslandWitness n k r} :
    P ∈ sourcePressureCanonicalPackingPairFamily L lo hi ↔
      P ∈ L.zip L.tail ∧
        SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2 := by
  classical
  simp [sourcePressureCanonicalPackingPairFamily]

/-- Canonical separator attached directly to an oriented witness-pair key. -/
def sourcePressureCanonicalPairSeparator
    {n : OddNat} {k r : ℕ}
    (P : SourcePressureLocalIslandWitness n k r ×
      SourcePressureLocalIslandWitness n k r) : ℕ :=
  r + P.1.val + 1

/-- The extracted canonical pair family satisfies the sharp half-window bound. -/
theorem sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressureCanonicalPackingPairFamily L lo hi).card ≤
      (hi - lo) / 2 + 1 := by
  classical
  let F := sourcePressureCanonicalPackingPairFamily L lo hi
  let f := sourcePressureCanonicalPairSeparator (n := n) (k := k) (r := r)
  have hstate : ∀ P ∈ F,
      SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2 := by
    intro P hP
    exact (mem_sourcePressureCanonicalPackingPairFamily.1 hP).2
  have hinj : Set.InjOn f F := by
    intro P hP Q hQ hsep
    let uP : SourcePressureFiniteWindowPackingUnit L lo hi :=
      ⟨P.1, P.2, hstate P hP⟩
    let uQ : SourcePressureFiniteWindowPackingUnit L lo hi :=
      ⟨Q.1, Q.2, hstate Q hQ⟩
    have hu : uP = uQ :=
      SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
        hsorted (by
          simpa only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
            uP, uQ, f, sourcePressureCanonicalPairSeparator] using hsep)
    cases P
    cases Q
    simp_all [uP, uQ]
  have hcard : (F.image f).card = F.card :=
    Finset.card_image_iff.mpr hinj
  have hwindow : ∀ m ∈ F.image f, lo ≤ m ∧ m ≤ hi := by
    intro m hm
    rcases Finset.mem_image.1 hm with ⟨P, hP, rfl⟩
    simpa [f, sourcePressureCanonicalPairSeparator] using
      (hstate P hP).separator_in_window
  have hsep : ∀ a ∈ F.image f, ∀ b ∈ F.image f, a < b → a + 2 ≤ b := by
    intro a ha b hb hab
    rcases Finset.mem_image.1 ha with ⟨P, hP, rfl⟩
    rcases Finset.mem_image.1 hb with ⟨Q, hQ, rfl⟩
    let uP : SourcePressureFiniteWindowPackingUnit L lo hi :=
      ⟨P.1, P.2, hstate P hP⟩
    let uQ : SourcePressureFiniteWindowPackingUnit L lo hi :=
      ⟨Q.1, Q.2, hstate Q hQ⟩
    have hne : uP ≠ uQ := by
      intro hu
      have : f P = f Q := by
        simpa only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
          uP, uQ, f, sourcePressureCanonicalPairSeparator] using
          congrArg SourcePressureFiniteWindowPackingUnit.canonicalSeparator hu
      omega
    rcases uP.canonicalSeparator_two_separated_of_ne_of_sorted hsorted hne with
      hforward | hreverse
    · simpa only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
        uP, uQ, f, sourcePressureCanonicalPairSeparator] using hforward
    · simp only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
        uP, uQ] at hreverse
      simp only [f, sourcePressureCanonicalPairSeparator] at hab
      omega
  rw [← hcard]
  exact finset_card_le_half_window_add_one_of_twoSeparated
    (F.image f) hwindow hsep

/--
Exact coverage proposition still needed to turn canonical-pair density into a
bound for every positive center in the witness list.

Current state transitions produce at least one forward pair; they do not prove
that every positive in-window witness is the left endpoint of such a pair.
This named proposition is therefore the next coverage contract, not an
established consequence of `BeamSeed`, `SortedFailure`, or
`FailureResolution`.
-/
def SourcePressureCanonicalLeftCoverageInWindow
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) : Prop :=
  ∀ W, W ∈ L →
    lo ≤ r + W.val → r + W.val ≤ hi →
    0 < SourcePressureMarginInt n k (r + W.val) →
    ∃ W', SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'

/-!
## Positive centers and the explicit coverage residue

The packing family counts certified adjacent pairs, whereas the observable
list contains individual positive centers.  The definitions below keep the
gap between those two populations explicit.  Full coverage is used only by
the conditional theorems; all unconditional bounds retain a finite residue.
-/

/-- Explicit in-window local-island witnesses supplied by `L`. -/
noncomputable def sourcePressurePositiveWitnessesInWindow
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
  L.toFinset.filter fun W => lo ≤ r + W.val ∧ r + W.val ≤ hi

@[simp]
theorem mem_sourcePressurePositiveWitnessesInWindow
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r} :
    W ∈ sourcePressurePositiveWitnessesInWindow L lo hi ↔
      W ∈ L ∧ lo ≤ r + W.val ∧ r + W.val ≤ hi := by
  classical
  simp [sourcePressurePositiveWitnessesInWindow]

/-- Every selected witness has positive pressure margin at its center. -/
theorem sourcePressurePositiveWitnessesInWindow_center_margin_pos
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r}
    (_hW : W ∈ sourcePressurePositiveWitnessesInWindow L lo hi) :
    0 < SourcePressureMarginInt n k (r + W.val) := by
  have hlocal := (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
  exact hlocal.2.1

/-- Left endpoints represented by the canonical adjacent-pair family. -/
noncomputable def sourcePressureCanonicalLeftWitnessesInWindow
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
  (sourcePressureCanonicalPackingPairFamily L lo hi).image Prod.fst

/-- The recursive adjacent-pair address is exactly represented in `zip L L.tail`. -/
theorem sourcePressureAdjacentPairInList_mem_zip
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
    (W, W') ∈ L.zip L.tail := by
  induction L with
  | nil => exact False.elim h
  | cons A rest ih =>
      cases rest with
      | nil => exact False.elim h
      | cons B rest =>
          rcases h with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            simp
          · simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr (ih htail)

@[simp]
theorem mem_sourcePressureCanonicalLeftWitnessesInWindow
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W : SourcePressureLocalIslandWitness n k r} :
    W ∈ sourcePressureCanonicalLeftWitnessesInWindow L lo hi ↔
      ∃ W', SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' := by
  classical
  constructor
  · intro hW
    rcases Finset.mem_image.1 hW with ⟨P, hP, hfst⟩
    rcases P with ⟨PL, PR⟩
    change PL = W at hfst
    subst PL
    exact ⟨PR, (mem_sourcePressureCanonicalPackingPairFamily.1 hP).2⟩
  · rintro ⟨W', hstate⟩
    apply Finset.mem_image.2
    exact ⟨(W, W'), mem_sourcePressureCanonicalPackingPairFamily.2
      ⟨sourcePressureAdjacentPairInList_mem_zip hstate.adjacentPair, hstate⟩, rfl⟩

/-- In a strictly sorted witness list, a left entry has one immediate right neighbor. -/
theorem sourcePressureAdjacentPairInList_right_unique_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W₁' W₂' : SourcePressureLocalIslandWitness n k r}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h₁ : SourcePressureLocalIslandWitnessAdjacentPairInList L W W₁')
    (h₂ : SourcePressureLocalIslandWitnessAdjacentPairInList L W W₂') :
    W₁' = W₂' := by
  rcases sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
      hsorted h₁ h₂ with heq | horder
  · exact heq.2
  · have hlt₁ : W.val < W₁'.val :=
      sourcePressureLocalIslandWitnessBefore_val_lt
        (sourcePressureAdjacentPairInList_before_of_sorted hsorted h₁)
    have hlt₂ : W.val < W₂'.val :=
      sourcePressureLocalIslandWitnessBefore_val_lt
        (sourcePressureAdjacentPairInList_before_of_sorted hsorted h₂)
    rcases horder with h₁₂ | h₂₁ <;> omega

/-- Projection to the left endpoint is injective on canonical adjacent pairs. -/
theorem sourcePressureCanonicalPackingPairFamily_fst_injOn
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    Set.InjOn Prod.fst
      (↑(sourcePressureCanonicalPackingPairFamily L lo hi) :
        Set (SourcePressureLocalIslandWitness n k r ×
          SourcePressureLocalIslandWitness n k r)) := by
  intro P hP Q hQ hfst
  have hPstate := (mem_sourcePressureCanonicalPackingPairFamily.1 hP).2
  have hQstate := (mem_sourcePressureCanonicalPackingPairFamily.1 hQ).2
  cases P with
  | mk PL PR =>
      cases Q with
      | mk QL QR =>
          change PL = QL at hfst
          subst QL
          have hright : PR = QR :=
            sourcePressureAdjacentPairInList_right_unique_of_sorted hsorted
              hPstate.adjacentPair hQstate.adjacentPair
          subst QR
          rfl

/-- Canonical left endpoints and canonical pair keys have equal cardinality. -/
theorem sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ)
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card =
      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
  classical
  exact Finset.card_image_iff.mpr
    (sourcePressureCanonicalPackingPairFamily_fst_injOn hsorted)

/-- Full canonical-left coverage includes every selected positive witness. -/
theorem sourcePressurePositiveWitnesses_subset_canonicalLeft_of_coverage
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
    sourcePressurePositiveWitnessesInWindow L lo hi ⊆
      sourcePressureCanonicalLeftWitnessesInWindow L lo hi := by
  intro W hW
  rcases mem_sourcePressurePositiveWitnessesInWindow.1 hW with
    ⟨hmem, hlo, hhi⟩
  exact mem_sourcePressureCanonicalLeftWitnessesInWindow.2
    (hcoverage W hmem hlo hhi
      (sourcePressurePositiveWitnessesInWindow_center_margin_pos hW))

/-- Conditional all-positive half-window capacity. -/
theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_of_coverage
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (hi - lo) / 2 + 1 := by
  calc
    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card :=
      Finset.card_le_card
        (sourcePressurePositiveWitnesses_subset_canonicalLeft_of_coverage hcoverage)
    _ = (sourcePressureCanonicalPackingPairFamily L lo hi).card :=
      sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card L lo hi hsorted
    _ ≤ _ := sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one hsorted

/-- Conditional all-positive sign capacity. -/
theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_of_coverage
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (sourcePressureNonposPositionsInWindow n k lo hi).card := by
  classical
  let S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi) :=
    (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image fun P =>
      ⟨P.1.1, P.1.2, (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩
  have hScard : S.card =
      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
    rw [show S =
      (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image
        (fun P => ⟨P.1.1, P.1.2,
          (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩) from rfl]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro P _ Q _ h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg SourcePressureFiniteWindowPackingUnit.left h
      · exact congrArg SourcePressureFiniteWindowPackingUnit.right h
  calc
    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card :=
      Finset.card_le_card
        (sourcePressurePositiveWitnesses_subset_canonicalLeft_of_coverage hcoverage)
    _ = (sourcePressureCanonicalPackingPairFamily L lo hi).card :=
      sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card L lo hi hsorted
    _ = S.card := hScard.symm
    _ ≤ _ := sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions hsorted S

/-- Conditional all-positive local-Big surface. -/
theorem sourcePressurePositiveWitnesses_localBig_of_coverage
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
        (hi - lo) / 2 + 1 ∧
      (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
        (sourcePressureNonposPositionsInWindow n k lo hi).card :=
  ⟨sourcePressurePositiveWitnesses_card_le_half_window_add_one_of_coverage
      hsorted hcoverage,
    sourcePressurePositiveWitnesses_card_le_nonposPositions_of_coverage
      hsorted hcoverage⟩

/-- Positive witnesses not certified as canonical left endpoints. -/
noncomputable def sourcePressurePositiveCoverageResidue
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
  sourcePressurePositiveWitnessesInWindow L lo hi \
    sourcePressureCanonicalLeftWitnessesInWindow L lo hi

/-- Exact decomposition into certified canonical-left witnesses and residue. -/
theorem sourcePressurePositiveWitnesses_subset_canonicalLeft_union_residue
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)} :
    sourcePressurePositiveWitnessesInWindow L lo hi ⊆
      sourcePressureCanonicalLeftWitnessesInWindow L lo hi ∪
        sourcePressurePositiveCoverageResidue L lo hi := by
  classical
  intro W hW
  by_cases hC : W ∈ sourcePressureCanonicalLeftWitnessesInWindow L lo hi
  · exact Finset.mem_union_left _ hC
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hW, hC⟩)

/-- Unconditional center count: certified pairs plus the explicit residue. -/
theorem sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)} :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (sourcePressureCanonicalPackingPairFamily L lo hi).card +
        (sourcePressurePositiveCoverageResidue L lo hi).card := by
  calc
    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi ∪
          sourcePressurePositiveCoverageResidue L lo hi).card :=
      Finset.card_le_card
        sourcePressurePositiveWitnesses_subset_canonicalLeft_union_residue
    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card +
          (sourcePressurePositiveCoverageResidue L lo hi).card :=
      Finset.card_union_le _ _
    _ ≤ _ := by
      exact Nat.add_le_add_right Finset.card_image_le _

/-- Residue-corrected half-window capacity, requiring no coverage claim. -/
theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_add_residue
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (hi - lo) / 2 + 1 +
        (sourcePressurePositiveCoverageResidue L lo hi).card := by
  exact le_trans sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
    (Nat.add_le_add_right
      (sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one hsorted) _)

/-- Residue-corrected sign capacity, requiring no coverage claim. -/
theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_add_residue
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (sourcePressureNonposPositionsInWindow n k lo hi).card +
        (sourcePressurePositiveCoverageResidue L lo hi).card := by
  classical
  let S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi) :=
    (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image fun P =>
      ⟨P.1.1, P.1.2, (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩
  have hScard : S.card =
      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
    rw [show S =
      (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image
        (fun P => ⟨P.1.1, P.1.2,
          (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩) from rfl]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro P _ Q _ h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg SourcePressureFiniteWindowPackingUnit.left h
      · exact congrArg SourcePressureFiniteWindowPackingUnit.right h
  calc
    _ ≤ (sourcePressureCanonicalPackingPairFamily L lo hi).card +
          (sourcePressurePositiveCoverageResidue L lo hi).card :=
      sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
    _ = S.card + (sourcePressurePositiveCoverageResidue L lo hi).card := by
      rw [hScard]
    _ ≤ _ := Nat.add_le_add_right
      (sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions hsorted S) _

/-!
## Boundary of the current state API

The automaton states imported by this module select one diagnosed adjacent
pair.  They do not quantify over every entry of `L.zip L.tail`.  Consequently
they cannot, by themselves, show that every nonterminal positive witness is a
canonical left endpoint.  The precise missing universal contract is named
below.  Once a producer for it exists, ordinary list recursion can reduce the
coverage residue to the terminal endpoint; without it, a `card ≤ 1` residue
claim would silently strengthen an existential diagnosis into list coverage.
-/

/--
Every in-window nonterminal witness pair is certified by the canonical packing
state.  This is the exact pair-level bridge needed before the residue can be
reduced to a terminal-list boundary.
-/
def SourcePressureCanonicalNonterminalPairCoverageInWindow
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) : Prop :=
  ∀ W W',
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' →
    lo ≤ r + W.val → r + W.val ≤ hi →
    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'

/-- Pair coverage immediately certifies every addressed nonterminal witness. -/
theorem SourcePressureCanonicalNonterminalPairCoverageInWindow.certifies
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureCanonicalNonterminalPairCoverageInWindow L lo hi)
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hpair : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
    (hlo : lo ≤ r + W.val) (hhi : r + W.val ≤ hi) :
    W ∈ sourcePressureCanonicalLeftWitnessesInWindow L lo hi :=
  mem_sourcePressureCanonicalLeftWitnessesInWindow.2
    ⟨W', h W W' hpair hlo hhi⟩

end DkMath.Collatz
