/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessRealizableProfiles

#print "file: DkMath.ABC.GNExcessRealizedFibers"

namespace DkMath.ABC

/-! ## The realized profile image -/

/-- The finite set of excess profiles actually attained on `[0, X]`. -/
noncomputable def GNExcessRealizedProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) := by
  classical
  exact (Finset.Icc 0 X).image
    (fun a => GNExcessDepthProfileAt Q p b a)

/-- Membership in the realized profile image is exactly nonempty realizability.
-/
theorem mem_GNExcessRealizedProfileSpace_iff
    {Q : Finset ℕ} {p b X : ℕ}
    {excess : ∀ q ∈ Q, ℕ} :
    excess ∈ GNExcessRealizedProfileSpace Q p b X ↔
      GNExcessProfileRealized Q excess p b X := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨a, ha, hprofile⟩
    apply GNExcessProfileRealized.of_point
    exact Finset.mem_filter.mpr ⟨ha, hprofile⟩
  · intro h
    rcases GNExcessProfileRealized.exists_point h with ⟨a, ha⟩
    rcases Finset.mem_filter.mp ha with ⟨haI, haE⟩
    apply Finset.mem_image.mpr
    exact ⟨a, haI, haE⟩

/-- An interval point contributes its pointwise profile to the realized image.
-/
theorem point_profile_mem_realizedProfileSpace
    {Q : Finset ℕ} {p b X a : ℕ}
    (ha : a ∈ Finset.Icc 0 X) :
    GNExcessDepthProfileAt Q p b a ∈
      GNExcessRealizedProfileSpace Q p b X := by
  apply mem_GNExcessRealizedProfileSpace_iff.mpr
  apply GNExcessProfileRealized.of_point
  exact Finset.mem_filter.mpr ⟨ha, rfl⟩

/-- Every realized profile has an interval point in its exact fiber. -/
theorem realizedProfileSpace_exists_point
    {Q : Finset ℕ} {p b X : ℕ}
    {excess : ∀ q ∈ Q, ℕ}
    (h : excess ∈ GNExcessRealizedProfileSpace Q p b X) :
    ∃ a ∈ Finset.Icc 0 X,
      GNExcessDepthProfileAt Q p b a = excess := by
  classical
  rcases Finset.mem_image.mp h with ⟨a, ha, hprofile⟩
  exact ⟨a, ha, hprofile⟩

/-! ## Relation with the formal rectangular space -/

/-- The actual profile image is contained in the formal profile box. -/
theorem GNExcessRealizedProfileSpace_subset_depthProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) (hb : 0 < b) :
    GNExcessRealizedProfileSpace Q p b X ⊆
      GNExcessDepthProfileSpace Q p b X := by
  classical
  intro excess h
  rcases realizedProfileSpace_exists_point h with ⟨a, ha, rfl⟩
  exact GNExcessDepthProfileAt_mem_space hb (Finset.mem_Icc.mp ha).2

/-! ## Exact fibers are disjoint and cover the interval -/

/-- Distinct profiles have disjoint exact interval fibers. -/
theorem GNExactExcessProfileEvent_disjoint
    {Q : Finset ℕ} {e₁ e₂ : ∀ q ∈ Q, ℕ}
    {p b X : ℕ}
    (hne : e₁ ≠ e₂) :
    Disjoint
      (GNExactExcessProfileEvent Q e₁ p b X)
      (GNExactExcessProfileEvent Q e₂ p b X) := by
  rw [Finset.disjoint_left]
  intro a ha₁ ha₂
  have h₁ := (Finset.mem_filter.mp ha₁).2
  have h₂ := (Finset.mem_filter.mp ha₂).2
  exact hne (h₁.symm.trans h₂)

/-- Every interval point belongs to the exact fiber of its own profile. -/
theorem mem_GNExactExcessProfileEvent_profileAt
    {Q : Finset ℕ} {p b X a : ℕ}
    (ha : a ∈ Finset.Icc 0 X) :
    a ∈ GNExactExcessProfileEvent Q
      (GNExcessDepthProfileAt Q p b a) p b X := by
  exact Finset.mem_filter.mpr ⟨ha, rfl⟩

/-- The exact fibers over realized profiles cover precisely the interval. -/
theorem biUnion_GNExactExcessProfileEvent_eq_Icc
    (Q : Finset ℕ) (p b X : ℕ) :
    (GNExcessRealizedProfileSpace Q p b X).biUnion
        (fun excess => GNExactExcessProfileEvent Q excess p b X) =
      Finset.Icc 0 X := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨excess, _, haE⟩
    exact (Finset.mem_filter.mp haE).1
  · intro ha
    apply Finset.mem_biUnion.mpr
    refine ⟨GNExcessDepthProfileAt Q p b a,
      point_profile_mem_realizedProfileSpace ha, ?_⟩
    exact mem_GNExactExcessProfileEvent_profileAt ha

/-! ## Cardinal consequences -/

/-- The number of realized profiles is at most the number of interval points.
-/
theorem card_GNExcessRealizedProfileSpace_le_interval
    (Q : Finset ℕ) (p b X : ℕ) :
    (GNExcessRealizedProfileSpace Q p b X).card ≤ X + 1 := by
  classical
  calc
    (GNExcessRealizedProfileSpace Q p b X).card ≤
        (Finset.Icc 0 X).card := Finset.card_image_le
    _ = X + 1 := by simp [Nat.card_Icc]

/-- The exact fiber cardinalities partition the interval cardinality. -/
theorem sum_card_GNExactExcessProfileEvent_eq_interval
    (Q : Finset ℕ) (p b X : ℕ) :
    ∑ excess ∈ GNExcessRealizedProfileSpace Q p b X,
      (GNExactExcessProfileEvent Q excess p b X).card = X + 1 := by
  classical
  let S := GNExcessRealizedProfileSpace Q p b X
  let fiber := fun excess => GNExactExcessProfileEvent Q excess p b X
  have hdis : (↑S : Set (∀ q ∈ Q, ℕ)).PairwiseDisjoint fiber := by
    intro e he f hf hne
    exact GNExactExcessProfileEvent_disjoint hne
  have hcard : (S.biUnion fiber).card = ∑ e ∈ S, (fiber e).card :=
    Finset.card_biUnion hdis
  have hcover : S.biUnion fiber = Finset.Icc 0 X := by
    exact biUnion_GNExactExcessProfileEvent_eq_Icc Q p b X
  rw [← hcard, hcover]
  simp [Nat.card_Icc]

end DkMath.ABC
