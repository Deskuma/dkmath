/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessProfileOvercount

#print "file: DkMath.ABC.GNExcessRealizableProfiles"

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-! ## Realizability and height -/

/-- A finite excess profile is realized when its exact interval fiber is
nonempty.  This separates actual profiles from the rectangular formal space.
-/
def GNExcessProfileRealized
    (Q : Finset ℕ)
    (excess : ∀ q ∈ Q, ℕ)
    (p b X : ℕ) : Prop :=
  (GNExactExcessProfileEvent Q excess p b X).Nonempty

/-- The realizability predicate is definitionally the nonemptiness of the
exact profile fiber. -/
theorem GNExcessProfileRealized_iff
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ} {p b X : ℕ} :
    GNExcessProfileRealized Q excess p b X ↔
      (GNExactExcessProfileEvent Q excess p b X).Nonempty :=
  Iff.rfl

/-- A point in the exact fiber realizes its profile. -/
theorem GNExcessProfileRealized.of_point
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ} {p b X a : ℕ}
    (ha : a ∈ GNExactExcessProfileEvent Q excess p b X) :
    GNExcessProfileRealized Q excess p b X :=
  ⟨a, ha⟩

/-- Every realized profile has an interval point in its exact fiber. -/
theorem GNExcessProfileRealized.exists_point
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ} {p b X : ℕ}
    (h : GNExcessProfileRealized Q excess p b X) :
    ∃ a, a ∈ GNExactExcessProfileEvent Q excess p b X :=
  h

/-- A profile is height-admissible when its joint depth modulus fits below the
given height. -/
def GNExcessProfileHeightAdmissible
    (Q : Finset ℕ)
    (excess : ∀ q ∈ Q, ℕ)
    (H : ℕ) : Prop :=
  GNExcessJointDepthModulus Q excess ≤ H

/-- The height predicate unfolds to the defining modulus inequality. -/
theorem GNExcessProfileHeightAdmissible_iff
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ} {H : ℕ} :
    GNExcessProfileHeightAdmissible Q excess H ↔
      GNExcessJointDepthModulus Q excess ≤ H :=
  Iff.rfl

/-- A realized canonical cubic profile is compatible with the cubic height
bound `3 * (X + 1)^2`. -/
theorem GNExcessProfileRealized.cubic_heightAdmissible
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : GNExcessProfileRealized
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess 3 1 X) :
    GNExcessProfileHeightAdmissible
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess
      (3 * (X + 1)^2) := by
  exact GNExcess_cubic_realized_modulus_le_height h

/-! ## Realized large profiles -/

/-- The large-profile container restricted to profiles with a nonempty exact
interval fiber. -/
noncomputable def GNExcessRealizedLargeProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) := by
  classical
  exact (GNExcessLargeProfileSpace Q p b X).filter
    (fun excess => GNExcessProfileRealized Q excess p b X)

/-- Every realized large profile is a member of the historical rectangular
large-profile space. -/
theorem realizedLargeProfileSpace_subset_largeProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    GNExcessRealizedLargeProfileSpace Q p b X ⊆
      GNExcessLargeProfileSpace Q p b X := by
  classical
  exact Finset.filter_subset _ _

/-- Membership in the realized large-profile space means largeness together
with nonempty realization. -/
theorem mem_realizedLargeProfileSpace_iff
    {Q : Finset ℕ} {p b X : ℕ} {excess : ∀ q ∈ Q, ℕ} :
    excess ∈ GNExcessRealizedLargeProfileSpace Q p b X ↔
      excess ∈ GNExcessLargeProfileSpace Q p b X ∧
        GNExcessProfileRealized Q excess p b X := by
  classical
  simp [GNExcessRealizedLargeProfileSpace]

/-- Membership in the realized space supplies profile realizability. -/
theorem mem_realizedLargeProfileSpace_realized
    {Q : Finset ℕ} {p b X : ℕ} {excess : ∀ q ∈ Q, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace Q p b X) :
    GNExcessProfileRealized Q excess p b X := by
  exact (mem_realizedLargeProfileSpace_iff.mp h).2

/-- Membership in the realized space supplies the old large-profile
condition. -/
theorem mem_realizedLargeProfileSpace_large
    {Q : Finset ℕ} {p b X : ℕ} {excess : ∀ q ∈ Q, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace Q p b X) :
    excess ∈ GNExcessLargeProfileSpace Q p b X := by
  exact (mem_realizedLargeProfileSpace_iff.mp h).1

/-- Every realized canonical cubic large profile satisfies the joint height
restriction. -/
theorem mem_realizedLargeProfileSpace_cubic_heightAdmissible
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X) :
    GNExcessProfileHeightAdmissible
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess
      (3 * (X + 1)^2) := by
  exact GNExcessProfileRealized.cubic_heightAdmissible
    (mem_realizedLargeProfileSpace_realized h)

/-- The known two-prime ghost profile is excluded from the realized large
space, although it remains in the old rectangular large space. -/
theorem GNExcessTwoPrimeProfile_not_mem_realizedLargeProfileSpace
    {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) :
    GNExcessTwoPrimeProfile Q n ∉
      GNExcessRealizedLargeProfileSpace Q 3 1 (13^n) := by
  intro hmem
  have hreal := mem_realizedLargeProfileSpace_realized hmem
  change (GNExactExcessProfileEvent Q (GNExcessTwoPrimeProfile Q n)
    3 1 (13 ^ n)).Nonempty at hreal
  rw [GNExcessTwoPrimeProfile_event_eq_empty h7 h13 hn] at hreal
  exact Finset.not_nonempty_empty hreal

/-! ## Optional honest boundary shell -/

/-- The undivided boundary sum over realized large profiles only. -/
noncomputable def GNExcessRealizedLargeBoundaryProfileSum
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) : ℝ :=
  ∑ excess ∈ GNExcessRealizedLargeProfileSpace Q p b X,
    (((p - 1) ^
        (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) *
      Real.exp (t * GNExcessActiveProfileMass Q excess)

/-- Restricting the raw boundary sum to realized profiles can only decrease it.
-/
theorem GNExcessRealizedLargeBoundaryProfileSum_le
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) :
    GNExcessRealizedLargeBoundaryProfileSum Q p b X t ≤
      GNExcessLargeBoundaryProfileSum Q p b X t := by
  classical
  unfold GNExcessRealizedLargeBoundaryProfileSum
    GNExcessLargeBoundaryProfileSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (realizedLargeProfileSpace_subset_largeProfileSpace Q p b X)
    (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

end DkMath.ABC
