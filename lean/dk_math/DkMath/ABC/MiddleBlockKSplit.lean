/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.TailUnionBasic

#print "file: DkMath.ABC.MiddleBlockKSplit"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockIndependentTail.lean` から切り出した Kset small/large decomposition owner。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob

-- Ksmall / Klarge: split Kset X by k < 3 and k ≥ 3
def Ksmall (X : ℕ) : Finset ℕ := (Kset X).filter fun k => k < 3
def Klarge (X : ℕ) : Finset ℕ := (Kset X).filter fun k => 3 ≤ k

/-- Kset X を k<3 と k≥3 に分け、前者の個数は ≤ 3。 -/
lemma Kset_disjoint_union (X : ℕ) :
  Disjoint (Ksmall X) (Klarge X) ∧ (Ksmall X) ∪ (Klarge X) = Kset X := by
  classical
  constructor
  · -- 排反性: k<3 と 3≤k は排反
    refine Finset.disjoint_left.mpr fun k hkS hkL => ?_
    have ⟨hkK, hklt⟩ := Finset.mem_filter.1 hkS
    have ⟨_, hkle⟩ := Finset.mem_filter.1 hkL
    exact lt_irrefl k (lt_of_lt_of_le hklt hkle)
  · -- 分割の包含
    ext k; constructor
    · intro hk
      rcases Finset.mem_union.mp hk with hkS | hkL
      · exact (Finset.mem_filter.1 hkS).1
      · exact (Finset.mem_filter.1 hkL).1
    · intro hk
      have hkK : k ∈ Kset X := hk
      by_cases hklt : k < 3
      · -- build a proof k ∈ Ksmall X via simp on mem_filter, then place it into the union
        have hsmall : k ∈ Ksmall X := by simp [Ksmall, Finset.mem_filter, hkK, hklt]
        apply Finset.mem_union.mpr; left; exact hsmall
      · -- build a proof k ∈ Klarge X similarly and place it into the union
        have hkge : 3 ≤ k := Nat.not_lt.mp hklt
        have hlarge : k ∈ Klarge X := by simp [Klarge, Finset.mem_filter, hkK, hkge]
        apply Finset.mem_union.mpr; right; exact hlarge

/-- Ksmall の要素数は最大 3 -/
lemma card_Ksmall_le_three (X : ℕ) : (Ksmall X).card ≤ 3 := by
  classical
  -- Ksmall X ⊆ range 3 (i.e. {0,1,2}), since k < 3 for all k in Ksmall
  have hsub : (Ksmall X) ⊆ (Finset.range 3 : Finset ℕ) := by
    intro k hk
    have ⟨_, hklt⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_range.mpr hklt
  calc
    (Ksmall X).card ≤ (Finset.range 3).card := Finset.card_le_card hsub
    _ = 3 := by simp [Finset.card_range]

end Prob

end DkMath.ABC
