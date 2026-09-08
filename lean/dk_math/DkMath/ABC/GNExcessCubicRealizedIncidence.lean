/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicRealizedDyadic

/-!
# Exact witness/fiber coordinates for realized cubic moduli

This module identifies each realized dyadic shell with the image of its actual
canonical witnesses and partitions those witnesses by exact full-repeated
modulus fibers.  The declarations are finite-set identities; no incidence
sparsity estimate is asserted.
-/

namespace DkMath.ABC

/-! ## Witness and shell spaces -/

/-- The full repeated modulus attached to a canonical cubic point. -/
noncomputable def GNExcessCubicFullRepeatedModulus (a : ℕ) : ℕ :=
  GNNonExceptionalRepeatedPart 3 a 1

/-- Positive canonical points in `[1,X]` whose full repeated modulus is large. -/
noncomputable def GNExcessCubicRealizedLargeWitnessSpace (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun a => X + 1 < GNExcessCubicFullRepeatedModulus a)

theorem mem_GNExcessCubicRealizedLargeWitnessSpace_iff
    {X a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeWitnessSpace X ↔
      1 ≤ a ∧ a ≤ X ∧
        X + 1 < GNExcessCubicFullRepeatedModulus a := by
  simp [GNExcessCubicRealizedLargeWitnessSpace,
    GNExcessCubicFullRepeatedModulus, and_assoc]

/-- The realized large modulus space is exactly the image of actual witnesses. -/
theorem GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace
    (X : ℕ) :
    (GNExcessCubicRealizedLargeWitnessSpace X).image
        GNExcessCubicFullRepeatedModulus =
      GNExcessCubicRealizedLargeModulusSpace X := by
  classical
  ext M
  constructor
  · intro hM
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hM
    have ha' := mem_GNExcessCubicRealizedLargeWitnessSpace_iff.mp ha
    apply mem_GNExcessCubicRealizedLargeModulusSpace_of_fullRepeatedPart
      (X := X) (a := a) (M := GNExcessCubicFullRepeatedModulus a)
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, ha'.2.1⟩
    · rfl
    · exact ha'.2.2
  · intro hM
    obtain ⟨a, ha, haI, hEq⟩ :=
      GNExcessCubicRealizedLargeModulusSpace_exists_witness hM
    have haX : a ≤ X := (Finset.mem_Icc.mp haI).2
    have ha1 : 1 ≤ a := ha
    have haW : a ∈ GNExcessCubicRealizedLargeWitnessSpace X :=
      mem_GNExcessCubicRealizedLargeWitnessSpace_iff.mpr
        ⟨ha1, haX, by simpa [GNExcessCubicFullRepeatedModulus, hEq] using
          GNExcessCubicRealizedLargeModulusSpace_interval_lt hM⟩
    exact Finset.mem_image.mpr ⟨a, haW, hEq.symm⟩

/-- Canonical witnesses whose full repeated modulus lies in `[D,2D)`. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeWitnessSpace X).filter
    (fun a =>
      D ≤ GNExcessCubicFullRepeatedModulus a ∧
      GNExcessCubicFullRepeatedModulus a < 2 * D)

theorem mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeWitnessSpace X ∧
        D ≤ GNExcessCubicFullRepeatedModulus a ∧
        GNExcessCubicFullRepeatedModulus a < 2 * D := by
  simp [GNExcessCubicRealizedLargeModulusShellWitnessSpace]

/-- The shell witness image is exactly the realized modulus shell. -/
theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
        GNExcessCubicFullRepeatedModulus =
      GNExcessCubicRealizedLargeModulusShell X D := by
  classical
  ext M
  constructor
  · intro hM
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hM
    have haW := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp ha
    have hMspace : GNExcessCubicFullRepeatedModulus a ∈
        GNExcessCubicRealizedLargeModulusSpace X := by
      rw [← GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
      exact Finset.mem_image.mpr ⟨a, haW.1, rfl⟩
    exact mem_GNExcessCubicRealizedLargeModulusShell_iff.mpr
      ⟨hMspace, haW.2.1, haW.2.2⟩
  · intro hM
    have hMs := mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM
    have hImg : M ∈
        (GNExcessCubicRealizedLargeWitnessSpace X).image
          GNExcessCubicFullRepeatedModulus := by
      rw [GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
      exact hMs.1
    obtain ⟨a, haW, hEq⟩ := Finset.mem_image.mp hImg
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, hEq⟩
    exact mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mpr
      ⟨haW, hEq ▸ hMs.2.1, hEq ▸ hMs.2.2⟩

/-- Cardinality of the shell witness space. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellWitnessCount
    (X D : ℕ) : ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).card

theorem GNExcessCubicRealizedLargeModulusShellCount_le_witnessCount
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellCount X D ≤
      GNExcessCubicRealizedLargeModulusShellWitnessCount X D := by
  unfold GNExcessCubicRealizedLargeModulusShellCount
    GNExcessCubicRealizedLargeModulusShellWitnessCount
  rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell X D]
  exact Finset.card_image_le

/-! ## Exact full-repeated fibers -/

/-- The exact full-repeated witness fiber of `M` inside `[1,X]`. -/
noncomputable def GNExcessCubicFullRepeatedWitnessFiber
    (X M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun a => GNExcessCubicFullRepeatedModulus a = M)

theorem mem_GNExcessCubicFullRepeatedWitnessFiber_iff
    {X M a : ℕ} :
    a ∈ GNExcessCubicFullRepeatedWitnessFiber X M ↔
      1 ≤ a ∧ a ≤ X ∧ GNExcessCubicFullRepeatedModulus a = M := by
  simp [GNExcessCubicFullRepeatedWitnessFiber, and_assoc]

theorem GNExcessCubicFullRepeatedWitnessFiber_nonempty_of_mem_modulusSpace
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    (GNExcessCubicFullRepeatedWitnessFiber X M).Nonempty := by
  obtain ⟨a, ha, haI, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusSpace_exists_witness hM
  refine ⟨a, ?_⟩
  exact mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mpr
    ⟨ha, (Finset.mem_Icc.mp haI).2, by
      simpa [GNExcessCubicFullRepeatedModulus] using hEq.symm⟩

private theorem fullRepeated_fibers_pairwise_disjoint (X D : ℕ) :
    (↑(GNExcessCubicRealizedLargeModulusShell X D) : Set ℕ).PairwiseDisjoint
      (fun M => GNExcessCubicFullRepeatedWitnessFiber X M) := by
  intro M _ N _ hMN
  change Disjoint
    (GNExcessCubicFullRepeatedWitnessFiber X M)
    (GNExcessCubicFullRepeatedWitnessFiber X N)
  rw [Finset.disjoint_left]
  intro a haM haN
  have hM := (mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp haM).2.2
  have hN := (mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp haN).2.2
  exact hMN (hM.symm.trans hN)

/-- Shell witnesses are exactly the union of their exact modulus fibers. -/
theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_fibers
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShell X D).biUnion
        (fun M => GNExcessCubicFullRepeatedWitnessFiber X M) =
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨M, hM, haF⟩ := Finset.mem_biUnion.mp ha
    have hF := mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp haF
    have hShell := mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM
    have hlarge := GNExcessCubicRealizedLargeModulusSpace_interval_lt hShell.1
    have hW : a ∈ GNExcessCubicRealizedLargeWitnessSpace X := by
      apply mem_GNExcessCubicRealizedLargeWitnessSpace_iff.mpr
      exact ⟨hF.1, hF.2.1,
        by simpa [GNExcessCubicFullRepeatedModulus, hF.2.2.symm] using hlarge⟩
    exact mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mpr
      ⟨hW, hF.2.2 ▸ hShell.2.1, hF.2.2 ▸ hShell.2.2⟩
  · intro ha
    have hW := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp ha
    have hW' := mem_GNExcessCubicRealizedLargeWitnessSpace_iff.mp hW.1
    have hM : GNExcessCubicFullRepeatedModulus a ∈
        GNExcessCubicRealizedLargeModulusShell X D := by
      apply mem_GNExcessCubicRealizedLargeModulusShell_iff.mpr
      have hspace : GNExcessCubicFullRepeatedModulus a ∈
          GNExcessCubicRealizedLargeModulusSpace X := by
        rw [← GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
        exact Finset.mem_image.mpr ⟨a, hW.1, rfl⟩
      exact ⟨hspace, hW.2.1, hW.2.2⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨GNExcessCubicFullRepeatedModulus a, hM, ?_⟩
    exact mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mpr
      ⟨hW'.1, hW'.2.1, rfl⟩

/-- The shell witness count is the sum of exact modulus-fiber cardinalities. -/
theorem GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_fiberCards
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
      ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
        (GNExcessCubicFullRepeatedWitnessFiber X M).card := by
  classical
  unfold GNExcessCubicRealizedLargeModulusShellWitnessCount
  rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_fibers]
  exact Finset.card_biUnion (fullRepeated_fibers_pairwise_disjoint X D)

/-! ## Complement packet and spacing -/

/-- Every shell witness carries the canonical factorization/complement packet. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_complement_packet
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    1 ≤ a ∧ a ≤ X ∧
      D ≤ GNExcessCubicFullRepeatedModulus a ∧
      GNExcessCubicFullRepeatedModulus a < 2 * D ∧
      X + 1 < GNExcessCubicFullRepeatedModulus a ∧
      GNExcessCubicFullRepeatedModulus a * GNExcessCubicComplement a =
        a ^ 2 + 3 * a + 3 ∧
      Squarefree (GNExcessCubicComplement a) ∧
      Nat.Coprime (GNExcessCubicFullRepeatedModulus a)
        (GNExcessCubicComplement a) ∧
      GNExcessCubicComplement a ≤ X := by
  have h := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp ha
  have hW := mem_GNExcessCubicRealizedLargeWitnessSpace_iff.mp h.1
  have hMspace : GNExcessCubicFullRepeatedModulus a ∈
      GNExcessCubicRealizedLargeModulusSpace X := by
    rw [← GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
    exact Finset.mem_image.mpr ⟨a, h.1, rfl⟩
  have hlarge := GNExcessCubicRealizedLargeModulusSpace_interval_lt hMspace
  refine ⟨hW.1, hW.2.1, h.2.1, h.2.2, hW.2.2, ?_, ?_, ?_, ?_⟩
  · simpa [GNExcessCubicFullRepeatedModulus] using
      GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic a
  · exact squarefree_GNExcessCubicComplement a
  · simpa [GNExcessCubicFullRepeatedModulus] using
      coprime_GNNonExceptionalRepeatedPart_GNExcessCubicComplement a
  · apply GNExcessCubicComplement_le_of_large
      (a := a) (X := X) (M := GNExcessCubicFullRepeatedModulus a)
      (by omega) hW.2.1
    · simpa [GNExcessCubicFullRepeatedModulus] using
        GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic a
    · exact hlarge

/-- Two distinct witnesses in one exact full-repeated fiber obey the spacing
inequality from the canonical quadratic. -/
theorem GNExcessCubicFullRepeatedWitnessFiber_spacing
    {X M a b : ℕ} (ha : a ∈ GNExcessCubicFullRepeatedWitnessFiber X M)
    (hb : b ∈ GNExcessCubicFullRepeatedWitnessFiber X M) (hab : a < b) :
    M ≤ (b - a) * (a + b + 3) := by
  have ha' := mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp ha
  have hb' := mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp hb
  have hda : M ∣ a ^ 2 + 3 * a + 3 := by
    refine ⟨GNExcessCubicComplement a, ?_⟩
    have hEq := GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic a
    have hrep : GNNonExceptionalRepeatedPart 3 a 1 = M := by
      simpa [GNExcessCubicFullRepeatedModulus] using ha'.2.2
    rw [hrep] at hEq
    exact hEq.symm
  have hdb : M ∣ b ^ 2 + 3 * b + 3 := by
    refine ⟨GNExcessCubicComplement b, ?_⟩
    have hEq := GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic b
    have hrep : GNNonExceptionalRepeatedPart 3 b 1 = M := by
      simpa [GNExcessCubicFullRepeatedModulus] using hb'.2.2
    rw [hrep] at hEq
    exact hEq.symm
  exact cubicQuadratic_commonDivisor_le_spacingProduct hab hda hdb

/-- Uniform interval version of exact fiber spacing. -/
theorem GNExcessCubicFullRepeatedWitnessFiber_spacing_le_interval
    {X M a b : ℕ} (ha : a ∈ GNExcessCubicFullRepeatedWitnessFiber X M)
    (hb : b ∈ GNExcessCubicFullRepeatedWitnessFiber X M) (hab : a < b) :
    M ≤ (b - a) * (2 * X + 3) := by
  apply le_trans (GNExcessCubicFullRepeatedWitnessFiber_spacing ha hb hab)
  have ha' := mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp ha
  have hb' := mem_GNExcessCubicFullRepeatedWitnessFiber_iff.mp hb
  apply Nat.mul_le_mul_left
  omega

/-- A multiplicative modulus condition gives a strict lower gap. -/
theorem GNExcessCubicFullRepeatedWitnessFiber_gap_gt_of_mul_lt_modulus
    {X M K a b : ℕ}
    (ha : a ∈ GNExcessCubicFullRepeatedWitnessFiber X M)
    (hb : b ∈ GNExcessCubicFullRepeatedWitnessFiber X M)
    (hab : a < b) (hK : K * (2 * X + 3) < M) : K < b - a := by
  have hs := GNExcessCubicFullRepeatedWitnessFiber_spacing_le_interval ha hb hab
  by_contra hgap
  have hle : b - a ≤ K := by omega
  have hmul := Nat.mul_le_mul_left (b - a) (show 2 * X + 3 ≤ 2 * X + 3 from le_rfl)
  have hbound : (b - a) * (2 * X + 3) ≤ K * (2 * X + 3) := by
    exact Nat.mul_le_mul_right _ hle
  omega

/-- The whole realized modulus space has no more points than its witness space. -/
theorem GNExcessCubicRealizedLargeModulusSpace_card_le_witnessSpace_card
    (X : ℕ) :
    (GNExcessCubicRealizedLargeModulusSpace X).card ≤
      (GNExcessCubicRealizedLargeWitnessSpace X).card := by
  rw [← GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
  exact Finset.card_image_le

end DkMath.ABC
