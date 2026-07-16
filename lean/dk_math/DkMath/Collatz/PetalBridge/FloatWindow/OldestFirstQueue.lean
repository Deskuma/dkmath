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

/-! ## Upper-tail characterization -/

/-- The oldest-first remainder lies above a cutoff exactly when its cardinality
fits inside the part of the original carrier above that cutoff. -/
theorem eraseOldestN_subset_filter_iff_card_le
    (c : ℕ) (s : Finset ℕ) (t : ℕ) :
    eraseOldestN c s ⊆ s.filter (fun x => t ≤ x) ↔
      (eraseOldestN c s).card ≤ (s.filter (fun x => t ≤ x)).card := by
  constructor
  · exact Finset.card_le_card
  · intro hcard y hy
    have hyS : y ∈ s := mem_of_mem_eraseOldestN hy
    apply Finset.mem_filter.mpr
    refine ⟨hyS, ?_⟩
    by_contra hty
    have hyLt : y < t := by omega
    have hUpperSub : s.filter (fun x => t ≤ x) ⊆ eraseOldestN c s := by
      intro x hx
      have hxS := (Finset.mem_filter.mp hx).1
      have htx := (Finset.mem_filter.mp hx).2
      have hxUnion : x ∈ consumedOldestN c s ∪ eraseOldestN c s := by
        rw [consumedOldestN_union_eraseOldestN]
        exact hxS
      rcases Finset.mem_union.mp hxUnion with hxConsumed | hxRemaining
      · have hxy := consumedOldestN_le_eraseOldestN c s x hxConsumed y hy
        omega
      · exact hxRemaining
    have hEq : s.filter (fun x => t ≤ x) = eraseOldestN c s :=
      Finset.eq_of_subset_of_card_le hUpperSub hcard
    have hyUpper : y ∈ s.filter (fun x => t ≤ x) := by
      rw [hEq]
      exact hy
    exact hty (Finset.mem_filter.mp hyUpper).2

/-- A same-cardinality subset is the oldest-first remainder whenever every
discarded source is no later than every retained source.  This is the generic
uniqueness theorem for the newest upper tail. -/
theorem eraseOldestN_eq_of_subset_card_and_complement_le
    {c : ℕ} {s u : Finset ℕ}
    (hu : u ⊆ s)
    (hcard : u.card = (eraseOldestN c s).card)
    (horder : ∀ x ∈ s \ u, ∀ y ∈ u, x ≤ y) :
    eraseOldestN c s = u := by
  apply Finset.Subset.antisymm
  · intro y hy
    by_contra hyu
    have hyS : y ∈ s := mem_of_mem_eraseOldestN hy
    have hyComp : y ∈ s \ u := Finset.mem_sdiff.mpr ⟨hyS, hyu⟩
    have hnotSub : ¬u ⊆ eraseOldestN c s := by
      intro hsub
      have hEq : u = eraseOldestN c s :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      exact hyu (by simpa [hEq] using hy)
    have hex : ∃ z, z ∈ u ∧ z ∉ eraseOldestN c s := by
      by_contra h
      apply hnotSub
      intro z hzU
      by_contra hzNot
      exact h ⟨z, hzU, hzNot⟩
    rcases hex with ⟨z, hzU, hzNot⟩
    have hzS : z ∈ s := hu hzU
    have hzUnion : z ∈ consumedOldestN c s ∪ eraseOldestN c s := by
      rw [consumedOldestN_union_eraseOldestN]
      exact hzS
    have hzConsumed : z ∈ consumedOldestN c s := by
      rcases Finset.mem_union.mp hzUnion with hz | hz
      · exact hz
      · exact False.elim (hzNot hz)
    have hzy := consumedOldestN_le_eraseOldestN c s z hzConsumed y hy
    have hyz := horder y hyComp z hzU
    have : y = z := Nat.le_antisymm hyz hzy
    subst z
    exact hzNot hy
  · intro y hy
    by_contra hyr
    have hyS : y ∈ s := hu hy
    have hyUnion : y ∈ consumedOldestN c s ∪ eraseOldestN c s := by
      rw [consumedOldestN_union_eraseOldestN]
      exact hyS
    have hyConsumed : y ∈ consumedOldestN c s := by
      rcases Finset.mem_union.mp hyUnion with hy' | hy'
      · exact hy'
      · exact False.elim (hyr hy')
    have hnotSub : ¬eraseOldestN c s ⊆ u := by
      intro hsub
      have hEq : eraseOldestN c s = u :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      exact hyr (by simpa [hEq] using hy)
    have hex : ∃ z, z ∈ eraseOldestN c s ∧ z ∉ u := by
      by_contra h
      apply hnotSub
      intro z hzR
      by_contra hzNot
      exact h ⟨z, hzR, hzNot⟩
    rcases hex with ⟨z, hzR, hzNot⟩
    have hzS : z ∈ s := mem_of_mem_eraseOldestN hzR
    have hzComp : z ∈ s \ u := Finset.mem_sdiff.mpr ⟨hzS, hzNot⟩
    have hyz := consumedOldestN_le_eraseOldestN c s y hyConsumed z hzR
    have hzy := horder z hzComp y hy
    have : y = z := Nat.le_antisymm hyz hzy
    subst z
    exact hzNot hy

/-! ## Threshold dominance -/

/-- Among all subsets of `s` with the same cardinality, the oldest-first
remainder retains the largest possible number of sources at or above every
cutoff.  This is the distributional form of FIFO source-age optimality. -/
theorem card_filter_le_card_filter_eraseOldestN
    {c : ℕ} {s u : Finset ℕ}
    (hu : u ⊆ s)
    (hcard : u.card = (eraseOldestN c s).card)
    (t : ℕ) :
    (u.filter (fun x => t ≤ x)).card ≤
      ((eraseOldestN c s).filter (fun x => t ≤ x)).card := by
  let r := eraseOldestN c s
  let upper := s.filter (fun x => t ≤ x)
  by_cases hru : r.card ≤ upper.card
  · have hrSub : r ⊆ upper :=
      (eraseOldestN_subset_filter_iff_card_le c s t).2 hru
    have hrFilter : r.filter (fun x => t ≤ x) = r := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact (Finset.mem_filter.mp (hrSub hx)).2
    rw [show eraseOldestN c s = r by rfl, hrFilter, ← hcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · have hUpperSub : upper ⊆ r := by
      intro x hx
      by_contra hxr
      have hxS := (Finset.mem_filter.mp hx).1
      have htx := (Finset.mem_filter.mp hx).2
      have hxConsumed : x ∈ consumedOldestN c s := by
        have hxUnion : x ∈ consumedOldestN c s ∪ r := by
          rw [show r = eraseOldestN c s by rfl,
            consumedOldestN_union_eraseOldestN]
          exact hxS
        exact (Finset.mem_union.mp hxUnion).resolve_right hxr
      have hex : ∃ y, y ∈ r ∧ y < t := by
        by_contra h
        push Not at h
        have hrSub : r ⊆ upper := by
          intro y hy
          exact Finset.mem_filter.mpr
            ⟨mem_of_mem_eraseOldestN hy, h y hy⟩
        have := Finset.card_le_card hrSub
        omega
      rcases hex with ⟨y, hyR, hyt⟩
      have hxy := consumedOldestN_le_eraseOldestN c s x hxConsumed y hyR
      omega
    have hUpperFilter : r.filter (fun x => t ≤ x) = upper := by
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_filter.mpr
          ⟨mem_of_mem_eraseOldestN (Finset.mem_filter.mp hx).1,
            (Finset.mem_filter.mp hx).2⟩
      · intro x hx
        exact Finset.mem_filter.mpr ⟨hUpperSub hx, (Finset.mem_filter.mp hx).2⟩
    rw [show eraseOldestN c s = r by rfl, hUpperFilter]
    exact Finset.card_le_card fun x hx =>
      Finset.mem_filter.mpr ⟨hu (Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2⟩

/-! ## Cardinality does not control age in an arbitrary queue -/

/-- Abstract queue retaining one source forever.  It is intentionally
Collatz-independent and serves only as a semantic regression. -/
def persistentSingletonQueue (_m : ℕ) : Finset ℕ :=
  {0}

@[simp] theorem card_persistentSingletonQueue (m : ℕ) :
    (persistentSingletonQueue m).card = 1 := by
  simp [persistentSingletonQueue]

/-- The persistent singleton has a uniform cardinal bound. -/
theorem persistentSingletonQueue_card_le_one (m : ℕ) :
    (persistentSingletonQueue m).card ≤ 1 := by
  simp

/-- Despite its cardinality being constantly one, the source age `m - 0` is
unbounded.  Thus uniform source age is not a generic necessary condition for
uniform queue cardinality; additional arithmetic structure is essential. -/
theorem not_exists_uniformAge_persistentSingletonQueue :
    ¬ ∃ H, ∀ m i, i ∈ persistentSingletonQueue m → m - i ≤ H := by
  rintro ⟨H, h⟩
  have hage := h (H + 1) 0 (by simp [persistentSingletonQueue])
  omega

end DkMath
