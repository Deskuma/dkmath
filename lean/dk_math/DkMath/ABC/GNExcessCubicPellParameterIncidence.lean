/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicSquarefulPell

/-!
# Square-cube and Pell-parameter incidence ledger

This module records the canonical quotient coordinates of a squareful realized
modulus and partitions the finite shell witness space by the squarefree
parameter `T = oddPart M * S`.  The statements are exact finite identities and
deterministic support bounds; no estimate for the number of parameters or Pell
solutions is asserted.
-/

namespace DkMath.ABC

/-! ## Canonical squareful quotient -/

/-- The canonical quotient of the even part by the odd part. -/
noncomputable def GNExcessCubicSquarefulQuotient (M : ℕ) : ℕ :=
  evenPart M / oddPart M

theorem evenPart_eq_oddPart_mul_GNExcessCubicSquarefulQuotient
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    evenPart M = oddPart M * GNExcessCubicSquarefulQuotient M := by
  have hrd := oddPart_dvd_evenPart_of_squarefull hM hfull
  simpa [GNExcessCubicSquarefulQuotient] using (Nat.mul_div_cancel' hrd).symm

theorem squareful_eq_squareQuotient_sq_mul_oddPart_cube
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    M = (GNExcessCubicSquarefulQuotient M) ^ 2 * (oddPart M) ^ 3 := by
  obtain ⟨hdecomp, _, _⟩ := squareful_oddEven_packet hM hfull
  have hrec := evenPart_eq_oddPart_mul_GNExcessCubicSquarefulQuotient hM hfull
  calc
    M = oddPart M * (evenPart M) ^ 2 := hdecomp
    _ = (GNExcessCubicSquarefulQuotient M) ^ 2 * (oddPart M) ^ 3 := by
      rw [hrec]
      ring

/-! ## Realized square-cube packets and shell support -/

theorem GNExcessCubicRealizedLargeModulusSpace_squareCube_packet
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    0 < M ∧ squarefull M ∧
      Squarefree (oddPart M) ∧
      0 < oddPart M ∧
      0 < GNExcessCubicSquarefulQuotient M ∧
      M = (GNExcessCubicSquarefulQuotient M) ^ 2 * (oddPart M) ^ 3 := by
  have hpos := GNExcessCubicRealizedLargeModulusSpace_pos hM
  have hfull := GNExcessCubicRealizedLargeModulusSpace_squarefull hM
  have hcanon := squareful_eq_squareQuotient_sq_mul_oddPart_cube
    (Nat.ne_of_gt hpos) hfull
  have hsf := squarefree_oddPart M
  have hrpos : 0 < oddPart M := by
    by_contra hr
    have hr0 : oddPart M = 0 := Nat.eq_zero_of_not_pos hr
    rw [hr0] at hcanon
    simp at hcanon
    omega
  have hquotpos : 0 < GNExcessCubicSquarefulQuotient M := by
    by_contra hu
    have hu0 : GNExcessCubicSquarefulQuotient M = 0 :=
      Nat.eq_zero_of_not_pos hu
    rw [hu0] at hcanon
    simp at hcanon
    omega
  exact ⟨hpos, hfull, hsf, hrpos, hquotpos, hcanon⟩

theorem oddPart_cube_le_of_squarefull
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    (oddPart M) ^ 3 ≤ M := by
  have hcanon := squareful_eq_squareQuotient_sq_mul_oddPart_cube hM hfull
  have hu : 0 < GNExcessCubicSquarefulQuotient M := by
    by_contra hnot
    have hu0 : GNExcessCubicSquarefulQuotient M = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hzero : M = 0 := by
      simpa [hu0] using hcanon
    exact hM hzero
  have hu2 : 1 ≤ (GNExcessCubicSquarefulQuotient M) ^ 2 :=
    Nat.one_le_pow 2 (GNExcessCubicSquarefulQuotient M) hu
  calc
    (oddPart M) ^ 3 = 1 * (oddPart M) ^ 3 := by simp
    _ ≤ (GNExcessCubicSquarefulQuotient M) ^ 2 * (oddPart M) ^ 3 :=
      Nat.mul_le_mul_right _ hu2
    _ = M := hcanon.symm

theorem GNExcessCubicRealizedLargeModulusShell_oddPart_cube_lt
    {X D M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusShell X D) :
    (oddPart M) ^ 3 < 2 * D := by
  have hspace := GNExcessCubicRealizedLargeModulusShell_subset X D hM
  have hpos := GNExcessCubicRealizedLargeModulusSpace_pos hspace
  have hfull := GNExcessCubicRealizedLargeModulusSpace_squarefull hspace
  have hcube := oddPart_cube_le_of_squarefull (Nat.ne_of_gt hpos) hfull
  exact lt_of_le_of_lt hcube
    (mem_GNExcessCubicRealizedLargeModulusShell_iff.mp hM).2.2

/-! ## Pell parameter space -/

/-- The squarefree Pell parameter attached to an incidence pair `(M,S)`. -/
noncomputable def GNExcessCubicPellParameter (p : ℕ × ℕ) : ℕ :=
  oddPart p.1 * p.2

noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).image
    GNExcessCubicPellParameter

theorem mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff
    {X D T : ℕ} :
    T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D ↔
      ∃ M S, (M, S) ∈
        GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D ∧
        oddPart M * S = T := by
  simp [GNExcessCubicRealizedLargeModulusShellPellParameterSpace,
    GNExcessCubicPellParameter]

private theorem oddPart_pos_of_realized_pair
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    0 < oddPart M := by
  obtain ⟨hdecomp, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
  obtain ⟨a, ha, hpair, _, _, _, _, _, _, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hMpos : 0 < M := by
    have hM := congrArg Prod.fst hpair
    have hpacket := GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha
    omega
  by_contra hr
  have hr0 : oddPart M = 0 := Nat.eq_zero_of_not_pos hr
  rw [hr0] at hdecomp
  simp at hdecomp
  omega

theorem GNExcessCubicRealizedLargeModulusShellPellParameterSpace_pos
    {X D T : ℕ}
    (hT : T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) :
    0 < T := by
  obtain ⟨M, S, hMS, hT⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mp hT
  have hr := oddPart_pos_of_realized_pair hMS
  obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  rw [← hT]
  exact Nat.mul_pos hr hSpos

theorem GNExcessCubicRealizedLargeModulusShellPellParameterSpace_squarefree
    {X D T : ℕ}
    (hT : T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) :
    Squarefree T := by
  obtain ⟨M, S, hMS, hT⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mp hT
  rw [← hT]
  exact GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter hMS

theorem GNExcessCubicRealizedLargeModulusShellPellParameter_packet
    {X D T : ℕ}
    (hT : T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) :
    ∃ M S r, (M, S) ∈
        GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D ∧
      r = oddPart M ∧ T = r * S ∧ Squarefree r ∧
      r ^ 3 < 2 * D ∧ 1 ≤ S ∧ S ≤ X := by
  obtain ⟨M, S, hMS, hT⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mp hT
  obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hp := GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
  have hMsh : M ∈ GNExcessCubicRealizedLargeModulusShell X D := by
    rw [← GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_fst_image_eq_shell X D]
    exact Finset.mem_image.mpr ⟨(M, S), hMS, rfl⟩
  refine ⟨M, S, oddPart M, hMS, rfl, hT.symm, hp.2.1, ?_,
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hSpos), hSX⟩
  · exact GNExcessCubicRealizedLargeModulusShell_oddPart_cube_lt hMsh

/-! ## Pell-parameter witness fibers and exact partition -/

noncomputable def GNExcessCubicRealizedLargeModulusShellPellParameterFiber
    (X D T : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a =>
      oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a = T)

theorem mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff
    {X D T a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a = T := by
  simp [GNExcessCubicRealizedLargeModulusShellPellParameterFiber]

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonempty
    {X D T : ℕ}
    (hT : T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) :
    (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).Nonempty := by
  obtain ⟨M, S, hMS, hT⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mp hT
  obtain ⟨a, ha, hpair, _, _, _, _, _, _, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hM : GNExcessCubicFullRepeatedModulus a = M := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
  have hS : GNExcessCubicComplement a = S := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.snd hpair
  refine ⟨a, mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr
    ⟨ha, ?_⟩⟩
  simpa [hM, hS] using hT

private theorem pellParameter_fibers_pairwise_disjoint (X D : ℕ) :
    (↑(GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) : Set ℕ).PairwiseDisjoint
      (fun T => GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T) := by
  intro T _ U _ hTU
  change Disjoint
    (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T)
    (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D U)
  rw [Finset.disjoint_left]
  intro a haT haU
  have hT :=
    (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp haT).2
  have hU :=
    (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp haU).2
  exact hTU (hT.symm.trans hU)

theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_pellParameterFibers
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D).biUnion
        (fun T => GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T) =
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨T, hT, haF⟩ := Finset.mem_biUnion.mp ha
    exact
      (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp haF).1
  · intro ha
    apply Finset.mem_biUnion.mpr
    let T := oddPart (GNExcessCubicFullRepeatedModulus a) *
      GNExcessCubicComplement a
    refine ⟨T, ?_, ?_⟩
    · apply mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mpr
      refine ⟨GNExcessCubicFullRepeatedModulus a,
        GNExcessCubicComplement a, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · rfl
    · exact mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr
        ⟨ha, rfl⟩

theorem GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_pellParameterFiberCards
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
      ∑ T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D,
        (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).card := by
  classical
  unfold GNExcessCubicRealizedLargeModulusShellWitnessCount
  rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_pellParameterFibers]
  exact Finset.card_biUnion (pellParameter_fibers_pairwise_disjoint X D)

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_equation
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T) :
    (2 * a + 3) ^ 2 + 3 =
      4 * T * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
  have hF := mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp ha
  have hpell := GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity
    hF.1 (show GNExcessCubicIncidencePair a =
      (GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a) from rfl)
  calc
    (2 * a + 3) ^ 2 + 3 =
        4 * (oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a) *
          (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := hpell
    _ = 4 * T * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
      rw [hF.2]

/-! ## Four-way finite ledger -/

theorem GNExcessCubicRealizedLargeModulusShell_four_way_card_ledger
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
        ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
          (GNExcessCubicFullRepeatedWitnessFiber X M).card ∧
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
        ∑ S ∈ GNExcessCubicRealizedLargeModulusShellComplementSpace X D,
          (GNExcessCubicRealizedLargeModulusShellComplementFiber X D S).card ∧
    (GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D).card =
      GNExcessCubicRealizedLargeModulusShellWitnessCount X D ∧
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
        ∑ T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D,
          (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).card := by
  exact ⟨GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_fiberCards X D,
    GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_complementFiberCards X D,
    GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_card X D,
    GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_pellParameterFiberCards X D⟩

end DkMath.ABC
