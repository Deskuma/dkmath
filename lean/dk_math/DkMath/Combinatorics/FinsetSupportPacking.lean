/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

#print "file: DkMath.Combinatorics.FinsetSupportPacking"

/-! A finite endpoint-deletion certificate for arbitrary support families. -/

namespace DkMath.Combinatorics

/-- Nonempty disjoint supports consume distinct directions in any containing universe. -/
theorem card_le_supportUniverse {α β : Type*}
    (R : Finset α) (f : α → Finset β) (T : Finset β)
    (hne : ∀ a ∈ R, (f a).Nonempty) (hsub : ∀ a ∈ R, f a ⊆ T)
    (hdisj : (R : Set α).PairwiseDisjoint f) : R.card ≤ T.card := by
  classical
  calc
    R.card = ∑ _a ∈ R, 1 := by simp
    _ ≤ ∑ a ∈ R, (f a).card := Finset.sum_le_sum (fun a ha => Finset.card_pos.mpr (hne a ha))
    _ = (R.biUnion f).card := (Finset.card_biUnion hdisj).symm
    _ ≤ T.card := Finset.card_le_card (by
      intro q hq
      obtain ⟨a, ha, hqa⟩ := Finset.mem_biUnion.mp hq
      exact hsub a ha hqa)

variable {α β : Type*} [LinearOrder α] [DecidableEq β]

/-- Each non-disjoint pair has exactly the orientation a < b. -/
noncomputable def supportCollisionEdges (V : Finset α) (f : α → Finset β) : Finset (α × α) := by
  classical
  exact (V.product V).filter (fun ab => ab.1 < ab.2 ∧ ¬ Disjoint (f ab.1) (f ab.2))

@[simp] theorem mem_supportCollisionEdges {V : Finset α} {f : α → Finset β} {a b : α} :
    (a, b) ∈ supportCollisionEdges V f ↔
      a ∈ V ∧ b ∈ V ∧ a < b ∧ ¬ Disjoint (f a) (f b) := by
  classical
  simp [supportCollisionEdges, and_assoc]

/-- The exact first-endpoint carrier used by deletion packing. -/
noncomputable def supportCollisionDeletionVertices (V : Finset α) (f : α → Finset β) : Finset α :=
  (supportCollisionEdges V f).image Prod.fst

/-- The deterministic remainder after deleting all first endpoints. -/
noncomputable def supportPackingRemainder (V : Finset α) (f : α → Finset β) : Finset α :=
  V \ supportCollisionDeletionVertices V f

@[simp] theorem mem_supportCollisionDeletionVertices {V : Finset α} {f : α → Finset β} {a : α} :
    a ∈ supportCollisionDeletionVertices V f ↔ ∃ b, (a, b) ∈ supportCollisionEdges V f := by
  classical
  simp only [supportCollisionDeletionVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨x,b⟩, h, he⟩
    dsimp at he
    subst x
    exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact ⟨(a,b), h, rfl⟩

@[simp] theorem mem_supportPackingRemainder {V : Finset α} {f : α → Finset β} {a : α} :
    a ∈ supportPackingRemainder V f ↔ a ∈ V ∧ a ∉ supportCollisionDeletionVertices V f :=
  Finset.mem_sdiff

theorem supportCollisionDeletionVertices_subset (V : Finset α) (f : α → Finset β) :
    supportCollisionDeletionVertices V f ⊆ V := by
  intro a ha
  obtain ⟨b, hb⟩ := mem_supportCollisionDeletionVertices.mp ha
  exact (mem_supportCollisionEdges.mp hb).1

theorem supportPackingRemainder_subset (V : Finset α) (f : α → Finset β) :
    supportPackingRemainder V f ⊆ V := Finset.sdiff_subset

theorem disjoint_supportPackingRemainder_deletion (V : Finset α) (f : α → Finset β) :
    Disjoint (supportPackingRemainder V f) (supportCollisionDeletionVertices V f) :=
  (Finset.disjoint_sdiff).symm

theorem supportPackingRemainder_union_deletion (V : Finset α) (f : α → Finset β) :
    supportPackingRemainder V f ∪ supportCollisionDeletionVertices V f = V :=
  Finset.sdiff_union_of_subset (supportCollisionDeletionVertices_subset V f)

theorem card_supportPacking_partition (V : Finset α) (f : α → Finset β) :
    V.card = (supportPackingRemainder V f).card + (supportCollisionDeletionVertices V f).card :=
  (Finset.card_sdiff_add_card_eq_card (supportCollisionDeletionVertices_subset V f)).symm

theorem card_supportCollisionDeletionVertices_le_edges (V : Finset α) (f : α → Finset β) :
    (supportCollisionDeletionVertices V f).card ≤ (supportCollisionEdges V f).card :=
  Finset.card_image_le

/-- First-endpoint deletion removes an endpoint of every remaining possible collision. -/
theorem supportPackingRemainder_pairwiseDisjoint (V : Finset α) (f : α → Finset β) :
    (supportPackingRemainder V f : Set α).PairwiseDisjoint f := by
  intro a ha b hb hne
  have ha' := mem_supportPackingRemainder.mp ha
  have hb' := mem_supportPackingRemainder.mp hb
  by_contra hdisj
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact ha'.2 (mem_supportCollisionDeletionVertices.mpr ⟨b,
      mem_supportCollisionEdges.mpr ⟨ha'.1, hb'.1, hab, hdisj⟩⟩)
  · exact hb'.2 (mem_supportCollisionDeletionVertices.mpr ⟨a,
      mem_supportCollisionEdges.mpr ⟨hb'.1, ha'.1, hba, fun h => hdisj h.symm⟩⟩)

/-- The exact generic certificate packet for the named deterministic remainder. -/
theorem supportPacking_exact_packet (V : Finset α) (f : α → Finset β) :
    supportPackingRemainder V f ⊆ V ∧
      (supportPackingRemainder V f : Set α).PairwiseDisjoint f ∧
      V.card = (supportPackingRemainder V f).card + (supportCollisionDeletionVertices V f).card :=
  ⟨supportPackingRemainder_subset V f, supportPackingRemainder_pairwiseDisjoint V f,
    card_supportPacking_partition V f⟩

/-- Optional opposite orientation: delete second rather than first endpoints. -/
noncomputable def supportCollisionRightDeletionVertices (V : Finset α) (f : α → Finset β) : Finset α :=
  (supportCollisionEdges V f).image Prod.snd

noncomputable def supportPackingRightRemainder (V : Finset α) (f : α → Finset β) : Finset α :=
  V \ supportCollisionRightDeletionVertices V f

@[simp] theorem mem_supportCollisionRightDeletionVertices {V : Finset α} {f : α → Finset β} {b : α} :
    b ∈ supportCollisionRightDeletionVertices V f ↔ ∃ a, (a,b) ∈ supportCollisionEdges V f := by
  classical
  simp only [supportCollisionRightDeletionVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨a,y⟩, h, he⟩
    dsimp at he
    subst y
    exact ⟨a, h⟩
  · rintro ⟨a, h⟩
    exact ⟨(a,b), h, rfl⟩

theorem supportCollisionRightDeletionVertices_subset (V : Finset α) (f : α → Finset β) :
    supportCollisionRightDeletionVertices V f ⊆ V := by
  intro b hb
  obtain ⟨a, ha⟩ := mem_supportCollisionRightDeletionVertices.mp hb
  exact (mem_supportCollisionEdges.mp ha).2.1

theorem card_supportPackingRight_partition (V : Finset α) (f : α → Finset β) :
    V.card = (supportPackingRightRemainder V f).card +
      (supportCollisionRightDeletionVertices V f).card :=
  (Finset.card_sdiff_add_card_eq_card (supportCollisionRightDeletionVertices_subset V f)).symm

theorem supportPackingRightRemainder_pairwiseDisjoint (V : Finset α) (f : α → Finset β) :
    (supportPackingRightRemainder V f : Set α).PairwiseDisjoint f := by
  intro a ha b hb hne
  have ha' := Finset.mem_sdiff.mp ha
  have hb' := Finset.mem_sdiff.mp hb
  by_contra hdisj
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact hb'.2 (mem_supportCollisionRightDeletionVertices.mpr ⟨a,
      mem_supportCollisionEdges.mpr ⟨ha'.1, hb'.1, hab, hdisj⟩⟩)
  · exact ha'.2 (mem_supportCollisionRightDeletionVertices.mpr ⟨b,
      mem_supportCollisionEdges.mpr ⟨hb'.1, ha'.1, hba, fun h => hdisj h.symm⟩⟩)

/-- The unchanged weak proposition now delegates to the exact public carrier. -/
theorem exists_supportPacking (V : Finset α) (f : α → Finset β) :
    ∃ R ⊆ V, (R : Set α).PairwiseDisjoint f ∧
      V.card ≤ R.card + (supportCollisionEdges V f).card := by
  refine ⟨supportPackingRemainder V f, supportPackingRemainder_subset V f,
    supportPackingRemainder_pairwiseDisjoint V f, ?_⟩
  rw [card_supportPacking_partition V f]
  exact Nat.add_le_add_left (card_supportCollisionDeletionVertices_le_edges V f) _

end DkMath.Combinatorics
