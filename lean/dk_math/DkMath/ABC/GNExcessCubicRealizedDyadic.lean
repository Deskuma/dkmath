/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicIncidenceObstruction

/-!
# Exact dyadic bookkeeping for realized cubic moduli

This module partitions the finite realized modulus space into the half-open
shells `[2^k, 2^(k+1))`.  The identities here are deterministic finite-set
bookkeeping.  No estimate for a shell count is assumed or proved.
-/

namespace DkMath.ABC

/-! ## Shells and their finite moments -/

/-- Realized moduli in the half-open shell `[D,2D)`. -/
noncomputable def GNExcessCubicRealizedLargeModulusShell
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusSpace X).filter
    (fun M => D ≤ M ∧ M < 2 * D)

theorem mem_GNExcessCubicRealizedLargeModulusShell_iff
    {X D M : ℕ} :
    M ∈ GNExcessCubicRealizedLargeModulusShell X D ↔
      M ∈ GNExcessCubicRealizedLargeModulusSpace X ∧
        D ≤ M ∧ M < 2 * D := by
  simp [GNExcessCubicRealizedLargeModulusShell]

theorem GNExcessCubicRealizedLargeModulusShell_subset
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShell X D ⊆
      GNExcessCubicRealizedLargeModulusSpace X := by
  intro M hM
  exact (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM).1

/-- The number of realized moduli in a shell. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellCount
    (X D : ℕ) : ℕ :=
  (GNExcessCubicRealizedLargeModulusShell X D).card

/-- The exact realized `3/8` moment contributed by one shell. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellMoment
    (X D : ℕ) : ℝ :=
  ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
    (M : ℝ) ^ (3 / 8 : ℝ)

private theorem shell_lower_weight
    {X D M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusShell X D) :
    (D : ℝ) ^ (3 / 8 : ℝ) ≤ (M : ℝ) ^ (3 / 8 : ℝ) := by
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact_mod_cast (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM).2.1

private theorem shell_upper_weight
    {X D M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusShell X D) :
    (M : ℝ) ^ (3 / 8 : ℝ) ≤ ((2 * D : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact_mod_cast (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM).2.2.le

/-! ## Deterministic shell weight bounds -/

theorem GNExcessCubicRealizedLargeModulusShell_card_mul_lowerWeight_le_moment
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellCount X D : ℝ) *
        (D : ℝ) ^ (3 / 8 : ℝ) ≤
      GNExcessCubicRealizedLargeModulusShellMoment X D := by
  classical
  unfold GNExcessCubicRealizedLargeModulusShellCount
    GNExcessCubicRealizedLargeModulusShellMoment
  calc
    ((GNExcessCubicRealizedLargeModulusShell X D).card : ℝ) *
        (D : ℝ) ^ (3 / 8 : ℝ) =
      ∑ _M ∈ GNExcessCubicRealizedLargeModulusShell X D,
        (D : ℝ) ^ (3 / 8 : ℝ) := by simp
    _ ≤ ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
        (M : ℝ) ^ (3 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro M hM
      exact shell_lower_weight hM

theorem GNExcessCubicRealizedLargeModulusShell_moment_le_card_mul_upperWeight
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellMoment X D ≤
      (GNExcessCubicRealizedLargeModulusShellCount X D : ℝ) *
        ((2 * D : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
  classical
  unfold GNExcessCubicRealizedLargeModulusShellCount
    GNExcessCubicRealizedLargeModulusShellMoment
  calc
    ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
        (M : ℝ) ^ (3 / 8 : ℝ) ≤
      ∑ _M ∈ GNExcessCubicRealizedLargeModulusShell X D,
        ((2 * D : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro M hM
      exact shell_upper_weight hM
    _ = ((GNExcessCubicRealizedLargeModulusShell X D).card : ℝ) *
        ((2 * D : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by simp

theorem GNExcessCubicRealizedLargeModulusShell_moment_le_of_card_le
    {X D : ℕ} {B : ℝ}
    (hB : (GNExcessCubicRealizedLargeModulusShellCount X D : ℝ) ≤ B) :
    GNExcessCubicRealizedLargeModulusShellMoment X D ≤
      B * ((2 * D : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
  calc
    _ ≤ (GNExcessCubicRealizedLargeModulusShellCount X D : ℝ) *
        ((2 * D : ℕ) : ℝ) ^ (3 / 8 : ℝ) :=
      GNExcessCubicRealizedLargeModulusShell_moment_le_card_mul_upperWeight X D
    _ ≤ _ := mul_le_mul_of_nonneg_right hB
      (Real.rpow_nonneg (by positivity) _)

/-! ## Dyadic indices and the exact partition -/

/-- Dyadic indices actually represented by realized moduli. -/
noncomputable def GNExcessCubicRealizedLargeDyadicIndexSpace
    (X : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusSpace X).image (Nat.log 2)

theorem mem_GNExcessCubicRealizedLargeDyadicIndexSpace_iff
    {X k : ℕ} :
    k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X ↔
      ∃ M ∈ GNExcessCubicRealizedLargeModulusSpace X,
        Nat.log 2 M = k := by
  simp [GNExcessCubicRealizedLargeDyadicIndexSpace]

theorem GNExcessCubicRealizedLargeModulus_dyadic_bounds
    {X M : ℕ} (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    2 ^ Nat.log 2 M ≤ M ∧ M < 2 ^ (Nat.log 2 M + 1) := by
  have hpos : M ≠ 0 :=
    (GNExcessCubicRealizedLargeModulusSpace_pos hM).ne'
  exact ⟨Nat.pow_log_le_self 2 hpos,
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) M⟩

private theorem dyadic_shells_pairwise_disjoint (X : ℕ) :
    (↑(GNExcessCubicRealizedLargeDyadicIndexSpace X) : Set ℕ).PairwiseDisjoint
      (fun k => GNExcessCubicRealizedLargeModulusShell X (2 ^ k)) := by
  intro i hi j hj hij
  change Disjoint
    (GNExcessCubicRealizedLargeModulusShell X (2 ^ i))
    (GNExcessCubicRealizedLargeModulusShell X (2 ^ j))
  rw [Finset.disjoint_left]
  intro M hMi hMj
  have hiM := (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hMi).2
  have hjM := (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hMj).2
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hiupper : M < 2 ^ (i + 1) := by
      simpa [Nat.pow_succ, Nat.mul_comm] using hiM.2
    omega
  · exact (hij rfl).elim
  · have hp : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hjupper : M < 2 ^ (j + 1) := by
      simpa [Nat.pow_succ, Nat.mul_comm] using hjM.2
    omega

theorem GNExcessCubicRealizedLargeModulus_dyadicShell_biUnion_eq
    (X : ℕ) :
    (GNExcessCubicRealizedLargeDyadicIndexSpace X).biUnion
        (fun k => GNExcessCubicRealizedLargeModulusShell X (2 ^ k)) =
      GNExcessCubicRealizedLargeModulusSpace X := by
  classical
  ext M
  constructor
  · intro hM
    obtain ⟨k, hk, hMk⟩ := Finset.mem_biUnion.mp hM
    exact (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hMk).1
  · intro hM
    have hbounds := GNExcessCubicRealizedLargeModulus_dyadic_bounds hM
    have hk : Nat.log 2 M ∈
        GNExcessCubicRealizedLargeDyadicIndexSpace X := by
      exact Finset.mem_image.mpr ⟨M, hM, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 M, hk, ?_⟩
    apply mem_GNExcessCubicRealizedLargeModulusShell_iff.mpr
    refine ⟨hM, hbounds.1, ?_⟩
    simpa [Nat.pow_succ, Nat.mul_comm] using hbounds.2

/-- Exact reindexing of the realized modulus moment by its dyadic shells. -/
theorem GNExcessCubicRealizedLargeModulusMoment_eq_sum_dyadicShellMoments
    (X : ℕ) :
    GNExcessCubicRealizedLargeModulusMoment X =
      ∑ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
        GNExcessCubicRealizedLargeModulusShellMoment X (2 ^ k) := by
  classical
  rw [GNExcessCubicRealizedLargeModulusMoment_eq_sum_modulusSpace]
  rw [← GNExcessCubicRealizedLargeModulus_dyadicShell_biUnion_eq X]
  rw [Finset.sum_biUnion (dyadic_shells_pairwise_disjoint X)]
  rfl

/-! ## Provider-free finite shell consumer -/

theorem GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds
    {X : ℕ} (B : ℕ → ℝ)
    (hB : ∀ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
      (GNExcessCubicRealizedLargeModulusShellCount X (2 ^ k) : ℝ) ≤ B k) :
    GNExcessCubicRealizedLargeModulusMoment X ≤
      ∑ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
        B k * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
  rw [GNExcessCubicRealizedLargeModulusMoment_eq_sum_dyadicShellMoments]
  apply Finset.sum_le_sum
  intro k hk
  have hshell :=
    GNExcessCubicRealizedLargeModulusShell_moment_le_of_card_le
      (X := X) (D := 2 ^ k) (B := B k) (hB k hk)
  simpa [Nat.pow_succ, Nat.mul_comm] using hshell

/-! ## Empty shells and endpoint guards -/

theorem GNExcessCubicRealizedLargeModulusShell_eq_empty_of_height_lt
    {X D : ℕ} (hD : 3 * (X + 1) ^ 2 < D) :
    GNExcessCubicRealizedLargeModulusShell X D = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨M, hM⟩ := hne
  have hs := mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM
  have hheight := GNExcessCubicRealizedLargeModulusSpace_height_le hs.1
  omega

theorem GNExcessCubicRealizedLargeModulusShell_eq_empty_of_below_large
    {X D : ℕ} (hD : 2 * D ≤ X + 2) :
    GNExcessCubicRealizedLargeModulusShell X D = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨M, hM⟩ := hne
  have hs := mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM
  have hlarge := GNExcessCubicRealizedLargeModulusSpace_interval_lt hs.1
  omega

theorem GNExcessCubicRealizedLargeDyadicIndexSpace_endpoint_bounds
    {X k : ℕ}
    (hk : k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X) :
    X + 1 < 2 ^ (k + 1) ∧ 2 ^ k ≤ 3 * (X + 1) ^ 2 := by
  obtain ⟨M, hM, rfl⟩ :=
    (mem_GNExcessCubicRealizedLargeDyadicIndexSpace_iff.mp hk)
  have hbounds := GNExcessCubicRealizedLargeModulus_dyadic_bounds hM
  have hlarge := GNExcessCubicRealizedLargeModulusSpace_interval_lt hM
  have hheight := GNExcessCubicRealizedLargeModulusSpace_height_le hM
  exact ⟨lt_of_lt_of_le hlarge hbounds.2.le, hbounds.1.trans hheight⟩

end DkMath.ABC
