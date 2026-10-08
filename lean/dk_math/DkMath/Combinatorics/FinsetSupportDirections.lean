/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Combinatorics.FinsetSupportPacking
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

#print "file: DkMath.Combinatorics.FinsetSupportDirections"

/-! Neutral finite support accounting and endpoint semantics. -/
namespace DkMath.Combinatorics

open scoped BigOperators

noncomputable def supportedSeats {α β : Type*} (R : Finset α) (f : α → Finset β) : Finset α := by
  classical
  exact R.filter (fun a => (f a).Nonempty)

noncomputable def representedDirections {α β : Type*} [DecidableEq β] (R : Finset α) (f : α → Finset β) : Finset β := by
  classical
  exact R.biUnion f

def retainedExcess {α β : Type*} (R : Finset α) (f : α → Finset β) : ℕ :=
  ∑ a ∈ R, ((f a).card - 1)

noncomputable def emptySupportSeats {α β : Type*} (R : Finset α) (f : α → Finset β) : Finset α := by
  classical
  exact R.filter (fun a => f a = ∅)

theorem emptySupportSeats_union_supported {α β : Type*} [DecidableEq α] (R : Finset α) (f : α → Finset β) :
    emptySupportSeats R f ∪ supportedSeats R f = R := by
  classical
  ext a
  simp only [emptySupportSeats,supportedSeats,Finset.mem_union,Finset.mem_filter]
  by_cases h : (f a).Nonempty
  · simp [h,Finset.nonempty_iff_ne_empty.mp h]
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

theorem disjoint_emptySupportSeats_supported {α β : Type*} (R : Finset α) (f : α → Finset β) :
    Disjoint (emptySupportSeats R f) (supportedSeats R f) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  have he := (Finset.mem_filter.mp ha).2
  have hn := (Finset.mem_filter.mp hb).2
  rw [he] at hn
  exact Finset.not_nonempty_empty hn

theorem card_support_split {α β : Type*} (R : Finset α) (f : α → Finset β) :
    (emptySupportSeats R f).card + (supportedSeats R f).card = R.card := by
  classical
  rw [← Finset.card_union_of_disjoint (disjoint_emptySupportSeats_supported R f),
    emptySupportSeats_union_supported]

theorem card_support_sum {α β : Type*} (R : Finset α) (f : α → Finset β) :
    ∑ a ∈ R, (f a).card = (supportedSeats R f).card + retainedExcess R f := by
  classical
  unfold supportedSeats retainedExcess
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h : (f a).Nonempty
  · have hp := Finset.card_pos.mpr h
    simp only [ite_eq_left h]
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

theorem card_representedDirections {α β : Type*} [DecidableEq β] (R : Finset α) (f : α → Finset β)
    (hd : (R : Set α).PairwiseDisjoint f) :
    (representedDirections R f).card = (supportedSeats R f).card + retainedExcess R f := by
  classical
  rw [representedDirections, Finset.card_biUnion hd, card_support_sum]

theorem representedDirections_unique {α β : Type*} [DecidableEq β] (R : Finset α) (f : α → Finset β)
    (hd : (R : Set α).PairwiseDisjoint f) {q : β} (hq : q ∈ representedDirections R f) :
    ∃! a, a ∈ R ∧ q ∈ f a := by
  classical
  obtain ⟨a,ha,hqa⟩ := Finset.mem_biUnion.mp hq
  refine ⟨a,⟨ha,hqa⟩,?_⟩
  rintro b ⟨hb,hqb⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hd hb ha hne) hqb hqa

/-- Erase the unique maximum; valid for any linear order, including its dual. -/
theorem card_nonmaximum_add_indicator {α : Type*} [LinearOrder α] (F : Finset α) :
    (F.filter (fun a => ∃ b ∈ F, a < b)).card + (if F.Nonempty then 1 else 0) = F.card := by
  classical
  by_cases h : F.Nonempty
  · have he : F.filter (fun a => ∃ b ∈ F, a < b) = F.erase (F.max' h) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ha,b,hb,hab⟩
        exact ⟨ne_of_lt (lt_of_lt_of_le hab (Finset.le_max' F b hb)),ha⟩
      · rintro ⟨hne,ha⟩
        exact ⟨ha,F.max' h,Finset.max'_mem F h,lt_of_le_of_ne (Finset.le_max' F a ha) hne⟩
    rw [he,ite_eq_left h]
    exact Finset.card_erase_add_one (Finset.max'_mem F h)
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

open scoped Classical in
/-- Transpose finite witness fibers once, independently of endpoint orientation. -/
theorem sum_witness_cards {α β : Type*} [DecidableEq α]
    (V : Finset α) (T : Finset β) (G : β → Finset α) (hG : ∀ q ∈ T, G q ⊆ V) :
    ∑ a ∈ V, (T.filter (fun q => a ∈ G q)).card = ∑ q ∈ T, (G q).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_boole]
  have he : V.filter (fun a => a ∈ G q) = G q := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hG q hq h,h⟩⟩
  rw [he]
  simp only [Nat.cast_id]

/-- Endpoint retention means simultaneous maximality in every supporting fiber. -/
theorem mem_supportPackingRemainder_iff_maxima {α β : Type*} [LinearOrder α] [DecidableEq β]
    {V : Finset α} {f : α → Finset β} {a : α} (ha : a ∈ V) :
    a ∈ supportPackingRemainder V f ↔ ∀ q ∈ f a, ∀ b ∈ V, q ∈ f b → b ≤ a := by
  classical
  rw [mem_supportPackingRemainder]
  constructor
  · rintro ⟨_ha,hd⟩ q hqa b hb hqb
    by_contra hle
    apply hd
    refine mem_supportCollisionDeletionVertices.mpr ⟨b,
      mem_supportCollisionEdges.mpr ⟨ha,hb,lt_of_not_ge hle,?_⟩⟩
    intro hdisj
    exact Finset.disjoint_left.mp hdisj hqa hqb
  · intro hm
    refine ⟨ha,?_⟩
    rintro hd
    obtain ⟨b,hab⟩ := mem_supportCollisionDeletionVertices.mp hd
    obtain ⟨_ha,hb,hlt,hnd⟩ := mem_supportCollisionEdges.mp hab
    obtain ⟨q,hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    exact (not_lt_of_ge (hm q (Finset.mem_inter.mp hq).1 b hb (Finset.mem_inter.mp hq).2)) hlt

/-- The mirrored selector retains simultaneous minima, using the existing right carrier. -/
theorem mem_supportPackingRightRemainder_iff_minima {α β : Type*} [LinearOrder α] [DecidableEq β]
    {V : Finset α} {f : α → Finset β} {a : α} (ha : a ∈ V) :
    a ∈ supportPackingRightRemainder V f ↔ ∀ q ∈ f a, ∀ b ∈ V, q ∈ f b → a ≤ b := by
  classical
  rw [supportPackingRightRemainder, Finset.mem_sdiff]
  constructor
  · rintro ⟨_ha,hd⟩ q hqa b hb hqb
    by_contra hle
    apply hd
    refine mem_supportCollisionRightDeletionVertices.mpr ⟨b,
      mem_supportCollisionEdges.mpr ⟨hb,ha,lt_of_not_ge hle,?_⟩⟩
    intro hdisj
    exact Finset.disjoint_left.mp hdisj hqb hqa
  · intro hm
    refine ⟨ha,?_⟩
    rintro hd
    obtain ⟨b,hab⟩ := mem_supportCollisionRightDeletionVertices.mp hd
    obtain ⟨hb,_ha,hlt,hnd⟩ := mem_supportCollisionEdges.mp hab
    obtain ⟨q,hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    exact (not_lt_of_ge (hm q (Finset.mem_inter.mp hq).2 b hb (Finset.mem_inter.mp hq).1)) hlt

end DkMath.Combinatorics
