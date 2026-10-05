/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card

#print "file: DkMath.Combinatorics.FinsetSupportPacking"

/-! A finite endpoint-deletion certificate for arbitrary support families. -/

namespace DkMath.Combinatorics

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

/-- Delete the first endpoint of each edge. The image may be smaller than the edge set. -/
theorem exists_supportPacking (V : Finset α) (f : α → Finset β) :
    ∃ R ⊆ V, (R : Set α).PairwiseDisjoint f ∧
      V.card ≤ R.card + (supportCollisionEdges V f).card := by
  classical
  let E := supportCollisionEdges V f
  let D := E.image Prod.fst
  let R := V \ D
  have hRV : R ⊆ V := Finset.sdiff_subset
  have hfree : (R : Set α).PairwiseDisjoint f := by
    intro a ha b hb hne
    have ha' : a ∈ V ∧ a ∉ D := Finset.mem_sdiff.mp ha
    have hb' : b ∈ V ∧ b ∉ D := Finset.mem_sdiff.mp hb
    by_contra hdisj
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact ha'.2 (Finset.mem_image.mpr ⟨(a,b),
        mem_supportCollisionEdges.mpr ⟨ha'.1, hb'.1, hab, hdisj⟩, rfl⟩)
    · exact hb'.2 (Finset.mem_image.mpr ⟨(b,a),
        mem_supportCollisionEdges.mpr ⟨hb'.1, ha'.1, hba, fun h => hdisj h.symm⟩, rfl⟩)
  have hbound : V.card ≤ R.card + E.card := by
    have hdel : D.card ≤ E.card := Finset.card_image_le
    have hbase : V.card ≤ R.card + D.card := Finset.card_le_card_sdiff_add_card
    omega
  exact ⟨R, hRV, hfree, hbound⟩

end DkMath.Combinatorics
