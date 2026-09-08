/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicRealizedIncidence

/-!
# Complement slices and incidence-pair coordinates

This module freezes the exact two-coordinate geometry of a realized cubic
dyadic shell.  A witness is sent to its full repeated modulus and its
canonical squarefree complement.  The pair is injective because its product
recovers the canonical quadratic.  All shell statements below are finite-set
identities; no fiber bound or incidence sparsity estimate is asserted.
-/

namespace DkMath.ABC

/-! ## The canonical incidence pair -/

/-- The full repeated modulus and canonical complement attached to `a`. -/
noncomputable def GNExcessCubicIncidencePair (a : ℕ) : ℕ × ℕ :=
  (GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a)

@[simp] theorem GNExcessCubicIncidencePair_fst (a : ℕ) :
    (GNExcessCubicIncidencePair a).1 =
      GNExcessCubicFullRepeatedModulus a := rfl

@[simp] theorem GNExcessCubicIncidencePair_snd (a : ℕ) :
    (GNExcessCubicIncidencePair a).2 = GNExcessCubicComplement a := rfl

/-- The pair product is the canonical quadratic value. -/
theorem GNExcessCubicIncidencePair_mul_eq_quadratic (a : ℕ) :
    (GNExcessCubicIncidencePair a).1 * (GNExcessCubicIncidencePair a).2 =
      a ^ 2 + 3 * a + 3 := by
  simpa [GNExcessCubicIncidencePair, GNExcessCubicFullRepeatedModulus] using
    GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic a

/-- The exact pair `(M(a), S(a))` identifies the canonical witness. -/
theorem GNExcessCubicIncidencePair_injective :
    Function.Injective GNExcessCubicIncidencePair := by
  intro a b hab
  have hprod :
      (GNExcessCubicIncidencePair a).1 *
          (GNExcessCubicIncidencePair a).2 =
        (GNExcessCubicIncidencePair b).1 *
          (GNExcessCubicIncidencePair b).2 := by
    exact congrArg (fun p : ℕ × ℕ => p.1 * p.2) hab
  apply cubicQuadratic_injective
  calc
    a ^ 2 + 3 * a + 3 =
        (GNExcessCubicIncidencePair a).1 *
          (GNExcessCubicIncidencePair a).2 :=
      (GNExcessCubicIncidencePair_mul_eq_quadratic a).symm
    _ = (GNExcessCubicIncidencePair b).1 *
          (GNExcessCubicIncidencePair b).2 := hprod
    _ = b ^ 2 + 3 * b + 3 :=
      GNExcessCubicIncidencePair_mul_eq_quadratic b

/-! ## Complement support and fibers -/

/-- Complement values actually represented in one realized shell. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellComplementSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
    GNExcessCubicComplement

theorem mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff
    {X D S : ℕ} :
    S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D ↔
      ∃ a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D,
        GNExcessCubicComplement a = S := by
  simp [GNExcessCubicRealizedLargeModulusShellComplementSpace]

private theorem complement_pos_of_shell_witness
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    0 < GNExcessCubicComplement a := by
  rcases GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha with
    ⟨ha1, _, _, _, hlarge, hEq, _, _, _⟩
  have hMpos : 0 < GNExcessCubicFullRepeatedModulus a := by omega
  have hquadpos : 0 < a ^ 2 + 3 * a + 3 := by nlinarith
  have hprodne :
      GNExcessCubicFullRepeatedModulus a * GNExcessCubicComplement a ≠ 0 := by
    intro hzero
    rw [hEq] at hzero
    exact (Nat.ne_of_gt hquadpos) hzero
  have hSne : GNExcessCubicComplement a ≠ 0 := by
    intro hS
    apply hprodne
    simp [hS]
  exact Nat.pos_of_ne_zero hSne

theorem GNExcessCubicRealizedLargeModulusShellComplementSpace_pos
    {X D S : ℕ}
    (hS : S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D) :
    0 < S := by
  obtain ⟨a, ha, rfl⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mp hS
  exact complement_pos_of_shell_witness ha

theorem GNExcessCubicRealizedLargeModulusShellComplementSpace_le
    {X D S : ℕ}
    (hS : S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D) :
    S ≤ X := by
  obtain ⟨a, ha, rfl⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mp hS
  exact (GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha).2.2.2.2.2.2.2.2

theorem GNExcessCubicRealizedLargeModulusShellComplementSpace_squarefree
    {X D S : ℕ}
    (hS : S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D) :
    Squarefree S := by
  obtain ⟨a, ha, rfl⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mp hS
  exact (GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha).2.2.2.2.2.2.1

theorem GNExcessCubicRealizedLargeModulusShellComplementSpace_subset_Icc
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellComplementSpace X D ⊆
      Finset.Icc 1 X := by
  intro S hS
  exact Finset.mem_Icc.mpr
    ⟨GNExcessCubicRealizedLargeModulusShellComplementSpace_pos hS,
      GNExcessCubicRealizedLargeModulusShellComplementSpace_le hS⟩

/-- Exact shell witness fiber at a fixed complement value. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellComplementFiber
    (X D S : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => GNExcessCubicComplement a = S)

theorem mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff
    {X D S a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellComplementFiber X D S ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        GNExcessCubicComplement a = S := by
  simp [GNExcessCubicRealizedLargeModulusShellComplementFiber]

theorem GNExcessCubicRealizedLargeModulusShellComplementFiber_nonempty
    {X D S : ℕ}
    (hS : S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D) :
    (GNExcessCubicRealizedLargeModulusShellComplementFiber X D S).Nonempty := by
  obtain ⟨a, ha, hSa⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mp hS
  refine ⟨a, mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff.mpr
    ⟨ha, hSa⟩⟩

private theorem complement_fibers_pairwise_disjoint (X D : ℕ) :
    (↑(GNExcessCubicRealizedLargeModulusShellComplementSpace X D) : Set ℕ).PairwiseDisjoint
      (fun S => GNExcessCubicRealizedLargeModulusShellComplementFiber X D S) := by
  intro S _ T _ hST
  change Disjoint
    (GNExcessCubicRealizedLargeModulusShellComplementFiber X D S)
    (GNExcessCubicRealizedLargeModulusShellComplementFiber X D T)
  rw [Finset.disjoint_left]
  intro a haS haT
  have hS :=
    (mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff.mp haS).2
  have hT :=
    (mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff.mp haT).2
  exact hST (hS.symm.trans hT)

theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_complementFibers
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellComplementSpace X D).biUnion
        (fun S => GNExcessCubicRealizedLargeModulusShellComplementFiber X D S) =
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨S, hS, haF⟩ := Finset.mem_biUnion.mp ha
    exact (mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff.mp haF).1
  · intro ha
    apply Finset.mem_biUnion.mpr
    refine ⟨GNExcessCubicComplement a, ?_, ?_⟩
    · exact mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mpr
        ⟨a, ha, rfl⟩
    · exact mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff.mpr
        ⟨ha, rfl⟩

theorem GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_complementFiberCards
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
      ∑ S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D,
        (GNExcessCubicRealizedLargeModulusShellComplementFiber X D S).card := by
  classical
  unfold GNExcessCubicRealizedLargeModulusShellWitnessCount
  rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_complementFibers]
  exact Finset.card_biUnion (complement_fibers_pairwise_disjoint X D)

/-! ## Shell incidence-pair space -/

/-- The exact finite set of represented `(M,S)` pairs in a shell. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellIncidencePairSpace
    (X D : ℕ) : Finset (ℕ × ℕ) :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
    GNExcessCubicIncidencePair

theorem mem_GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_iff
    {X D M S : ℕ} :
    (M, S) ∈ GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D ↔
      ∃ a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D,
        GNExcessCubicIncidencePair a = (M, S) := by
  simp [GNExcessCubicRealizedLargeModulusShellIncidencePairSpace]

theorem GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_card
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).card =
      GNExcessCubicRealizedLargeModulusShellWitnessCount X D := by
  unfold GNExcessCubicRealizedLargeModulusShellIncidencePairSpace
    GNExcessCubicRealizedLargeModulusShellWitnessCount
  exact Finset.card_image_iff.mpr GNExcessCubicIncidencePair_injective.injOn

theorem GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_fst_image_eq_shell
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).image Prod.fst =
      GNExcessCubicRealizedLargeModulusShell X D := by
  classical
  ext M
  constructor
  · intro hM
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell X D]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · intro hM
    rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell X D] at hM
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hM
    apply Finset.mem_image.mpr
    refine ⟨GNExcessCubicIncidencePair a, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · simp [hEq]

theorem GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_snd_image_eq_complementSpace
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).image Prod.snd =
      GNExcessCubicRealizedLargeModulusShellComplementSpace X D := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mpr
      ⟨a, ha, rfl⟩
  · intro hS
    obtain ⟨a, ha, hEq⟩ :=
      mem_GNExcessCubicRealizedLargeModulusShellComplementSpace_iff.mp hS
    apply Finset.mem_image.mpr
    refine ⟨GNExcessCubicIncidencePair a, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · simp [hEq]

theorem GNExcessCubicRealizedLargeModulusShellCount_le_incidencePairSpace_card
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellCount X D ≤
      (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).card := by
  unfold GNExcessCubicRealizedLargeModulusShellCount
  rw [← GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_fst_image_eq_shell X D]
  exact Finset.card_image_le

theorem GNExcessCubicRealizedLargeModulusShellComplementSpace_card_le_incidencePairSpace_card
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellComplementSpace X D).card ≤
      (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).card := by
  rw [← GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_snd_image_eq_complementSpace X D]
  exact Finset.card_image_le

/-! ## Exact pair packets and fixed-complement consumers -/

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_packet
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    ∃ a,
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
      GNExcessCubicIncidencePair a = (M, S) ∧
      1 ≤ a ∧ a ≤ X ∧ D ≤ M ∧ M < 2 * D ∧ X + 1 < M ∧
      0 < S ∧ S ≤ X ∧ Squarefree S ∧ Nat.Coprime M S ∧
      M * S = a ^ 2 + 3 * a + 3 := by
  obtain ⟨a, ha, hpair⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_iff.mp hMS
  have hM : GNExcessCubicFullRepeatedModulus a = M := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
  have hS : GNExcessCubicComplement a = S := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.snd hpair
  rcases GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha with
    ⟨ha1, haX, hD, h2D, hlarge, hEq, hSq, hCop, hSX⟩
  have hSpos : 0 < S := by simpa [hS] using complement_pos_of_shell_witness ha
  refine ⟨a, ha, hpair, ha1, haX, ?_, ?_, ?_, hSpos, ?_, ?_, ?_, ?_⟩
  · simpa [hM] using hD
  · simpa [hM] using h2D
  · simpa [hM] using hlarge
  · simpa [hS] using hSX
  · simpa [hS] using hSq
  · simpa [hM, hS] using hCop
  · simpa [hM, hS] using hEq

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_existsUnique_witness
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    ∃! a,
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
      GNExcessCubicIncidencePair a = (M, S) := by
  obtain ⟨a, ha, hpair⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_iff.mp hMS
  refine ⟨a, ⟨ha, hpair⟩, ?_⟩
  intro b hb
  exact GNExcessCubicIncidencePair_injective (hb.2.trans hpair.symm)

theorem GNExcessCubicRealizedLargeModulusShellComplementFiber_equation
    {X D S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellComplementFiber X D S) :
    GNExcessCubicFullRepeatedModulus a * S = a ^ 2 + 3 * a + 3 ∧
      D ≤ GNExcessCubicFullRepeatedModulus a ∧
      GNExcessCubicFullRepeatedModulus a < 2 * D := by
  have hF := mem_GNExcessCubicRealizedLargeModulusShellComplementFiber_iff.mp ha
  have hP := GNExcessCubicRealizedLargeModulusShellWitness_complement_packet hF.1
  rcases hP with ⟨_, _, hD, h2D, _, hEq, _, _, _⟩
  have hS := hF.2
  refine ⟨?_, hD, h2D⟩
  simpa [hS] using hEq

/-! ## The exact three-way finite ledger -/

theorem GNExcessCubicRealizedLargeModulusShell_three_way_card_ledger
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
        ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
          (GNExcessCubicFullRepeatedWitnessFiber X M).card ∧
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
        ∑ S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D,
          (GNExcessCubicRealizedLargeModulusShellComplementFiber X D S).card ∧
    (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).card =
      GNExcessCubicRealizedLargeModulusShellWitnessCount X D := by
  exact ⟨GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_fiberCards X D,
    GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_complementFiberCards X D,
    GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_card X D⟩

end DkMath.ABC
