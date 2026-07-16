/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue"

namespace DkMath

/-!
# Oldest-first finite source queue

This module is independent of the Collatz definitions.  Natural numbers are
source times, so deleting the least member implements FIFO service while
preserving the identity of every unconsumed source.
-/

/-- Remove at most `c` least source times from a finite source set. -/
noncomputable def eraseOldestN : ℕ → Finset ℕ → Finset ℕ
  | 0, s => s
  | c + 1, s =>
      if h : s.Nonempty then
        eraseOldestN c (s.erase (s.min' h))
      else
        ∅

@[simp] theorem eraseOldestN_zero (s : Finset ℕ) :
    eraseOldestN 0 s = s := rfl

/-- Oldest-first service never introduces a source. -/
theorem eraseOldestN_subset (c : ℕ) (s : Finset ℕ) :
    eraseOldestN c s ⊆ s := by
  induction c generalizing s with
  | zero => simp
  | succ c ih =>
      rw [eraseOldestN]
      split_ifs with h
      · exact (ih _).trans (Finset.erase_subset _ _)
      · simp

/-- Oldest-first service removes exactly `min c s.card` sources. -/
theorem card_eraseOldestN (c : ℕ) (s : Finset ℕ) :
    (eraseOldestN c s).card = s.card - c := by
  induction c generalizing s with
  | zero => simp
  | succ c ih =>
      rw [eraseOldestN]
      split_ifs with h
      · rw [ih, Finset.card_erase_of_mem (Finset.min'_mem s h)]
        omega
      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [hs]

/-- Sources removed by oldest-first service. -/
noncomputable def consumedOldestN (c : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s \ eraseOldestN c s

/-- The consumed source count is exactly the available service. -/
theorem card_consumedOldestN (c : ℕ) (s : Finset ℕ) :
    (consumedOldestN c s).card = min c s.card := by
  rw [consumedOldestN,
    Finset.card_sdiff_of_subset (eraseOldestN_subset c s),
    card_eraseOldestN]
  by_cases h : c ≤ s.card
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (by omega)]
    omega

/-- Consumed and remaining source identities are disjoint. -/
theorem disjoint_consumedOldestN_eraseOldestN (c : ℕ) (s : Finset ℕ) :
    Disjoint (consumedOldestN c s) (eraseOldestN c s) := by
  exact Finset.sdiff_disjoint

/-- Consumed and remaining sources reconstruct the original source set. -/
theorem consumedOldestN_union_eraseOldestN (c : ℕ) (s : Finset ℕ) :
    consumedOldestN c s ∪ eraseOldestN c s = s := by
  unfold consumedOldestN
  exact Finset.sdiff_union_of_subset (eraseOldestN_subset c s)

/-- Membership in the remainder implies membership in the original set. -/
theorem mem_of_mem_eraseOldestN
    {c : ℕ} {s : Finset ℕ} {i : ℕ}
    (hi : i ∈ eraseOldestN c s) : i ∈ s :=
  eraseOldestN_subset c s hi

/--
FIFO invariant: every consumed source is no later than every source left in
the oldest-first remainder.
-/
theorem consumedOldestN_le_eraseOldestN
    (c : ℕ) (s : Finset ℕ) :
    ∀ x ∈ consumedOldestN c s, ∀ y ∈ eraseOldestN c s, x ≤ y := by
  induction c generalizing s with
  | zero => simp [consumedOldestN]
  | succ c ih =>
      rw [eraseOldestN]
      split_ifs with h
      · let m := s.min' h
        let s' := s.erase m
        intro x hx y hy
        have hyS' : y ∈ s' := eraseOldestN_subset c s' hy
        have hyS : y ∈ s := Finset.mem_of_mem_erase hyS'
        by_cases hxm : x = m
        · subst x
          exact Finset.min'_le s y hyS
        · have hxS : x ∈ s := (Finset.mem_sdiff.mp hx).1
          have hxS' : x ∈ s' := Finset.mem_erase.mpr ⟨hxm, hxS⟩
          have hxNotOld : x ∉ eraseOldestN (c + 1) s :=
            (Finset.mem_sdiff.mp hx).2
          have hxNot : x ∉ eraseOldestN c s' := by
            simpa [eraseOldestN, h, s', m] using hxNotOld
          exact ih s' x (Finset.mem_sdiff.mpr ⟨hxS', hxNot⟩) y hy
      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [hs, consumedOldestN]

/-!
## Policy comparison

Source time increases toward the present, so a smaller source is older.  The
following finite comparison is the useful minimax form of FIFO optimality: no
other subset of the original carrier with the same remainder cardinality can
make every retained source newer than one retained FIFO source.
-/

/-- Every same-cardinality alternative remainder contains a source no newer
than each chosen source in the oldest-first remainder. -/
theorem exists_le_of_card_eq_card_eraseOldestN
    {c : ℕ} {s t : Finset ℕ}
    (ht : t ⊆ s)
    (hcard : t.card = (eraseOldestN c s).card)
    {y : ℕ} (hy : y ∈ eraseOldestN c s) :
    ∃ x ∈ t, x ≤ y := by
  by_contra hnone
  push Not at hnone
  have hsub : t ⊆ (eraseOldestN c s).erase y := by
    intro x hx
    have hxs : x ∈ s := ht hx
    have hxUnion : x ∈ consumedOldestN c s ∪ eraseOldestN c s := by
      rw [consumedOldestN_union_eraseOldestN]
      exact hxs
    rcases Finset.mem_union.mp hxUnion with hxConsumed | hxRemaining
    · have hxy := consumedOldestN_le_eraseOldestN c s x hxConsumed y hy
      exact False.elim ((Nat.not_lt_of_ge hxy) (hnone x hx))
    · exact Finset.mem_erase.mpr ⟨by
        exact ne_of_gt (hnone x hx), hxRemaining⟩
  have hle := Finset.card_le_card hsub
  have hlt := Finset.card_erase_lt_of_mem hy
  have : (eraseOldestN c s).card < (eraseOldestN c s).card := by
    calc
      (eraseOldestN c s).card = t.card := hcard.symm
      _ ≤ ((eraseOldestN c s).erase y).card := hle
      _ < (eraseOldestN c s).card := hlt
  exact (Nat.lt_irrefl _ this)

end DkMath
