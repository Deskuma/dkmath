/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicThreeSector

/-!
# Finite three-sector incidence ledger

This module turns the LUNA-016 arithmetic split into exact finite filters,
images, fibers, and card identities.  It contains no multiplicity, density,
or sparsity estimate.
-/

namespace DkMath.ABC

/-! ## Fixed-parameter sector filters -/

noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree
    (X D T : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).filter
    (fun a => ¬ 3 ∣ a)

theorem mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_iff
    {X D T a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree X D T ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T ∧
        ¬ 3 ∣ a := by
  simp [GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree]

noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree
    (X D T : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).filter
    (fun a => 3 ∣ a)

theorem mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_iff
    {X D T a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree X D T ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T ∧
        3 ∣ a := by
  simp [GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree]

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_eq_nonThree_union_three
    (X D T : ℕ) :
    GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree X D T ∪
        GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree X D T =
      GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T := by
  ext a
  constructor
  · intro h
    exact (Finset.mem_union.mp h).elim
      (fun hN => (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_iff.mp hN).1)
      (fun h3 => (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_iff.mp h3).1)
  · intro h
    by_cases h3 : 3 ∣ a
    · exact Finset.mem_union.mpr (Or.inr
        (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_iff.mpr
          ⟨h, h3⟩))
    · exact Finset.mem_union.mpr (Or.inl
        (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_iff.mpr
          ⟨h, h3⟩))

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_disjoint_three
    (X D T : ℕ) :
    Disjoint
      (GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree X D T)
      (GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree X D T) := by
  rw [Finset.disjoint_left]
  intro a haN ha3
  exact (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_iff.mp haN).2
    (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_iff.mp ha3).2

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_card_eq_sector_cards
    (X D T : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).card =
      (GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree X D T).card +
        (GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree X D T).card := by
  rw [← GNExcessCubicRealizedLargeModulusShellPellParameterFiber_eq_nonThree_union_three]
  exact Finset.card_union_of_disjoint
    (GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_disjoint_three X D T)

/-! ## Fixed-parameter packet consumers -/

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_packet
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree X D T) :
    ¬ 3 ∣ a ∧ ¬ 3 ∣ 2 * a + 3 ∧ ¬ 3 ∣ T ∧
    Nat.Coprime (2 * a + 3) T ∧
    (2 * a + 3) ^ 2 + 3 =
      4 * T * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 ∧
    Nat.Coprime (2 * a + 3)
      (evenPart (GNExcessCubicFullRepeatedModulus a)) ∧
    Squarefree T := by
  have hmem := mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree_iff.mp ha
  have hp := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_primitive_packet
    hmem.1 hmem.2
  exact ⟨hmem.2, hp.1, hp.2.1, hp.2.2.2.1,
    hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_packet
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree X D T) :
    3 ∣ a ∧
    2 * a + 3 = 3 * GNExcessCubicThreeSectorY a ∧
    T = 3 * GNExcessCubicThreeSectorPellParameter T ∧
    ¬ 3 ∣ GNExcessCubicThreeSectorPellParameter T ∧
    Nat.Coprime (GNExcessCubicThreeSectorY a)
      (GNExcessCubicThreeSectorPellParameter T) ∧
    3 * (GNExcessCubicThreeSectorY a) ^ 2 + 1 =
      4 * (GNExcessCubicThreeSectorPellParameter T) *
        (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 ∧
    Nat.Coprime (GNExcessCubicThreeSectorY a)
      (evenPart (GNExcessCubicFullRepeatedModulus a)) := by
  have hmem := mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_iff.mp ha
  have hrec := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_reconstruction
    hmem.1 hmem.2
  have hcop := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_coprime
    hmem.1 hmem.2
  have heq := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_equation
    hmem.1 hmem.2
  exact ⟨hmem.2, hrec.1, hrec.2.2.1, hrec.2.2.2.2,
    hcop.1, heq, hcop.2⟩

/-! ## Normalized parameter image and support -/

noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorParameter
    (a : ℕ) : ℕ :=
  GNExcessCubicThreeSectorPellParameter
    (oddPart (GNExcessCubicFullRepeatedModulus a) *
      GNExcessCubicComplement a)

noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
      (fun a => 3 ∣ a) |>.image
    GNExcessCubicRealizedLargeModulusShellThreeSectorParameter

theorem mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace_iff
    {X D T3 : ℕ} :
    T3 ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace X D ↔
      ∃ a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D,
        3 ∣ a ∧
          T3 = GNExcessCubicRealizedLargeModulusShellThreeSectorParameter a := by
  constructor
  · intro h
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp h
    have ha' := Finset.mem_filter.mp ha
    exact ⟨a, ha'.1, ha'.2, hEq.symm⟩
  · rintro ⟨a, ha, ha3, hEq⟩
    apply Finset.mem_image.mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, ha3⟩, hEq.symm⟩

theorem GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace_packet
    {X D T3 : ℕ}
    (hT3 : T3 ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace X D) :
    0 < T3 ∧ Squarefree T3 ∧ ¬ 3 ∣ T3 := by
  obtain ⟨a, ha, ha3, hT3⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace_iff.mp hT3
  let T := oddPart (GNExcessCubicFullRepeatedModulus a) *
    GNExcessCubicComplement a
  have hTF : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr ⟨ha, rfl⟩
  have hrec := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_reconstruction
    hTF ha3
  have hTspace : T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D := by
    apply mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mpr
    exact ⟨GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a,
      Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
  have hEqT : T3 = GNExcessCubicThreeSectorPellParameter T := by
    simpa [T, GNExcessCubicRealizedLargeModulusShellThreeSectorParameter] using hT3
  have hTpos := GNExcessCubicRealizedLargeModulusShellPellParameterSpace_pos hTspace
  have hSqT := GNExcessCubicRealizedLargeModulusShellPellParameterSpace_squarefree hTspace
  have hdiv : T3 ∣ T := by
    calc
      T3 ∣ 3 * GNExcessCubicThreeSectorPellParameter T := by
        rw [← hEqT]
        exact ⟨3, by ring⟩
      _ = T := hrec.2.2.1.symm
  have hSqT3 : Squarefree T3 := hSqT.squarefree_of_dvd hdiv
  have hnotParam : ¬ 3 ∣ GNExcessCubicThreeSectorPellParameter T :=
    hrec.2.2.2.2
  have hposParam : 0 < GNExcessCubicThreeSectorPellParameter T := by
    omega
  have hposT3 : 0 < T3 := by simpa [hEqT] using hposParam
  have hnotT3 : ¬ 3 ∣ T3 := by simpa [hEqT] using hnotParam
  exact ⟨hposT3, hSqT3, hnotT3⟩

/-! ## Normalized three-sector fibers -/

noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber
    (X D T3 : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => 3 ∣ a ∧
      GNExcessCubicRealizedLargeModulusShellThreeSectorParameter a = T3)

theorem mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff
    {X D T3 a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3 ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        3 ∣ a ∧
        GNExcessCubicRealizedLargeModulusShellThreeSectorParameter a = T3 := by
  simp [GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber]

theorem GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_nonempty
    {X D T3 : ℕ}
    (hT3 : T3 ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace X D) :
    (GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3).Nonempty := by
  obtain ⟨a, ha, ha3, hEq⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace_iff.mp hT3
  exact ⟨a, mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff.mpr
    ⟨ha, ha3, hEq.symm⟩⟩

theorem GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_primitive_packet
    {X D T3 a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3) :
    3 ∣ a ∧
    2 * a + 3 = 3 * GNExcessCubicThreeSectorY a ∧
    T3 = GNExcessCubicThreeSectorPellParameter
      (oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a) ∧
    ¬ 3 ∣ T3 ∧
    Nat.Coprime (GNExcessCubicThreeSectorY a) T3 ∧
    3 * (GNExcessCubicThreeSectorY a) ^ 2 + 1 =
      4 * T3 * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 ∧
    Nat.Coprime (GNExcessCubicThreeSectorY a)
      (evenPart (GNExcessCubicFullRepeatedModulus a)) := by
  have hmem := mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff.mp ha
  let T := oddPart (GNExcessCubicFullRepeatedModulus a) *
    GNExcessCubicComplement a
  have hTF : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr ⟨hmem.1, rfl⟩
  have hpack := GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_packet
    (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree_iff.mpr
      ⟨hTF, hmem.2.1⟩)
  have hT3 : T3 = GNExcessCubicThreeSectorPellParameter T := by
    simpa [T, GNExcessCubicRealizedLargeModulusShellThreeSectorParameter] using hmem.2.2.symm
  refine ⟨hpack.1, hpack.2.1, hT3, ?_, ?_, ?_, ?_⟩
  · simpa [hT3] using hpack.2.2.2.1
  · simpa [hT3] using hpack.2.2.2.2.1
  · simpa [hT3] using hpack.2.2.2.2.2.1
  · exact hpack.2.2.2.2.2.2

theorem GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_equation
    {X D T3 a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3) :
    3 * (GNExcessCubicThreeSectorY a) ^ 2 + 1 =
      4 * T3 * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
  exact (GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_primitive_packet
    ha).2.2.2.2.2.1

/-! ## The normalized `T3` finite partition -/

private theorem threeSector_parameter_fibers_pairwise_disjoint (X D : ℕ) :
    (↑(GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace X D) : Set ℕ).PairwiseDisjoint
      (fun T3 => GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3) := by
  intro T3 _ U _ hTU
  change Disjoint
    (GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3)
    (GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D U)
  rw [Finset.disjoint_left]
  intro a haT haU
  have hT :=
    (mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff.mp haT).2.2
  have hU :=
    (mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff.mp haU).2.2
  exact hTU (hT.symm.trans hU)

noncomputable def GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => 3 ∣ a)

theorem mem_GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧ 3 ∣ a := by
  simp [GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace]

theorem GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_eq_biUnion_parameterFibers
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace X D).biUnion
        (fun T3 => GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3) =
      GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨T3, hT3, haF⟩ := Finset.mem_biUnion.mp ha
    have hf := mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff.mp haF
    exact mem_GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_iff.mpr
      ⟨hf.1, hf.2.1⟩
  · intro ha
    have hW := mem_GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_iff.mp ha
    let T3 := GNExcessCubicRealizedLargeModulusShellThreeSectorParameter a
    apply Finset.mem_biUnion.mpr
    refine ⟨T3, ?_, ?_⟩
    · exact mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace_iff.mpr
        ⟨a, hW.1, hW.2, rfl⟩
    · exact mem_GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber_iff.mpr
        ⟨hW.1, hW.2, rfl⟩

theorem GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_card_eq_sum_parameterFiberCards
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace X D).card =
      ∑ T3 ∈ GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace X D,
        (GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber X D T3).card := by
  classical
  rw [← GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace_eq_biUnion_parameterFibers]
  exact Finset.card_biUnion (threeSector_parameter_fibers_pairwise_disjoint X D)

/-! ## Shell-level sector partition -/

noncomputable def GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => ¬ 3 ∣ a)

noncomputable def GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace X D

theorem mem_GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧ ¬ 3 ∣ a := by
  simp [GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace]

theorem mem_GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧ 3 ∣ a := by
  simp [GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace,
    GNExcessCubicRealizedLargeModulusShellThreeSectorWitnessSpace]

theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_nonThree_union_three
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace X D ∪
        GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace X D =
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D := by
  ext a
  constructor
  · intro h
    exact (Finset.mem_union.mp h).elim
      (fun hN => (mem_GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace_iff.mp hN).1)
      (fun h3 => (mem_GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace_iff.mp h3).1)
  · intro h
    by_cases h3 : 3 ∣ a
    · exact Finset.mem_union.mpr (Or.inr
        (mem_GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace_iff.mpr ⟨h, h3⟩))
    · exact Finset.mem_union.mpr (Or.inl
        (mem_GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace_iff.mpr ⟨h, h3⟩))

theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_nonThree_disjoint_three
    (X D : ℕ) :
    Disjoint
      (GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace X D)
      (GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace X D) := by
  rw [Finset.disjoint_left]
  intro a haN ha3
  exact (mem_GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace_iff.mp haN).2
    (mem_GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace_iff.mp ha3).2

theorem GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_threeSector_split
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
      (GNExcessCubicRealizedLargeModulusShellNonThreeWitnessSpace X D).card +
        (GNExcessCubicRealizedLargeModulusShellThreeWitnessSpace X D).card := by
  unfold GNExcessCubicRealizedLargeModulusShellWitnessCount
  rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_nonThree_union_three]
  exact Finset.card_union_of_disjoint
    (GNExcessCubicRealizedLargeModulusShellWitnessSpace_nonThree_disjoint_three X D)

end DkMath.ABC
