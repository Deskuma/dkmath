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

end DkMath.Collatz
