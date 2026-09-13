/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicPrimitivePell

#print "file: DkMath.ABC.GNExcessCubicThreeSector"

/-!
# Exceptional-prime three-sector normalization

This module separates the exact `3`-sector of the cubic Pell packet.  It is
an arithmetic normalization only: no solution count, density, or sparsity
claim is made.
-/

namespace DkMath.ABC

theorem three_dvd_cubicQuadratic_iff (a : ℕ) :
    3 ∣ a ^ 2 + 3 * a + 3 ↔ 3 ∣ a := by
  have hform : a ^ 2 + 3 * a + 3 = a ^ 2 + (3 * a + 3) := by ring
  have hthree : 3 ∣ 3 * a + 3 := by
    refine ⟨a + 1, ?_⟩
    ring
  constructor
  · intro h
    have ha2 : 3 ∣ a ^ 2 := by
      have hs := Nat.dvd_sub h hthree
      convert hs using 1; omega
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three ha2
  · intro h
    rw [hform]
    exact dvd_add (dvd_pow h (by decide : (2 : ℕ) ≠ 0)) hthree

theorem three_dvd_pellY_iff (a : ℕ) :
    3 ∣ 2 * a + 3 ↔ 3 ∣ a := by
  constructor
  · intro h
    have h2a : 3 ∣ 2 * a := by
      have h3 : 3 ∣ 3 := dvd_refl 3
      have hs := Nat.dvd_sub h h3
      convert hs using 1; omega
    have hc : Nat.Coprime 3 2 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by norm_num)
    exact hc.dvd_of_dvd_mul_left h2a
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨2 * k + 1, ?_⟩
    omega

theorem cubicQuadratic_three_exact_depth_one {a : ℕ} (ha : 3 ∣ a) :
    3 ∣ a ^ 2 + 3 * a + 3 ∧ ¬ 9 ∣ a ^ 2 + 3 * a + 3 := by
  exact ⟨three_dvd_cubicQuadratic_iff a |>.2 ha,
    not_nine_dvd_GN_three_one a⟩

private theorem threeSector_shell_witness_modulus_space
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    GNExcessCubicFullRepeatedModulus a ∈
      GNExcessCubicRealizedLargeModulusSpace X := by
  have hMsh : GNExcessCubicFullRepeatedModulus a ∈
      GNExcessCubicRealizedLargeModulusShell X D := by
    rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell X D]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact GNExcessCubicRealizedLargeModulusShell_subset X D hMsh

theorem GNExcessCubicRealizedLargeModulusSpace_not_three_dvd
    {X M : ℕ} (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ¬ 3 ∣ M := by
  intro h
  have hm := GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one
    hM Nat.prime_three h
  norm_num at hm

theorem GNExcessCubicRealizedLargeModulusSpace_coprime_three
    {X M : ℕ} (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    Nat.Coprime M 3 :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
    (GNExcessCubicRealizedLargeModulusSpace_not_three_dvd hM)
      |>.symm)

theorem GNExcessCubicRealizedLargeModulusShellWitness_not_three_dvd_oddPart
    {X D a : ℕ} (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ¬ 3 ∣ oddPart (GNExcessCubicFullRepeatedModulus a) := by
  intro h
  exact GNExcessCubicRealizedLargeModulusSpace_not_three_dvd
    (threeSector_shell_witness_modulus_space ha)
      (dvd_trans h (oddPart_dvd_of_squarefull
        (Nat.ne_of_gt (GNExcessCubicRealizedLargeModulusSpace_pos
          (threeSector_shell_witness_modulus_space ha)))
        (GNExcessCubicRealizedLargeModulusSpace_squarefull
          (threeSector_shell_witness_modulus_space ha))))

theorem GNExcessCubicRealizedLargeModulusShellWitness_not_three_dvd_evenPart
    {X D a : ℕ} (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ¬ 3 ∣ evenPart (GNExcessCubicFullRepeatedModulus a) := by
  intro h
  exact GNExcessCubicRealizedLargeModulusSpace_not_three_dvd
    (threeSector_shell_witness_modulus_space ha)
      (dvd_trans h (evenPart_dvd_of_squarefull
        (Nat.ne_of_gt (GNExcessCubicRealizedLargeModulusSpace_pos
          (threeSector_shell_witness_modulus_space ha)))
        (GNExcessCubicRealizedLargeModulusSpace_squarefull
          (threeSector_shell_witness_modulus_space ha))))

theorem GNExcessCubicRealizedLargeModulusShellWitness_not_three_dvd_squarefulQuotient
    {X D a : ℕ} (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ¬ 3 ∣ GNExcessCubicSquarefulQuotient
      (GNExcessCubicFullRepeatedModulus a) := by
  intro h
  exact GNExcessCubicRealizedLargeModulusSpace_not_three_dvd
    (threeSector_shell_witness_modulus_space ha)
      (dvd_trans h (GNExcessCubicSquarefulQuotient_dvd_of_squarefull
        (Nat.ne_of_gt (GNExcessCubicRealizedLargeModulusSpace_pos
          (threeSector_shell_witness_modulus_space ha)))
        (GNExcessCubicRealizedLargeModulusSpace_squarefull
          (threeSector_shell_witness_modulus_space ha))))

theorem GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_complement_iff
    {X D a : ℕ} (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    3 ∣ GNExcessCubicComplement a ↔ 3 ∣ a := by
  obtain ⟨ha1, haX, hD, h2D, hlarge, hEq, hSq, hCop, hSX⟩ :=
    GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha
  let M := GNExcessCubicFullRepeatedModulus a
  let S := GNExcessCubicComplement a
  have hMspace := threeSector_shell_witness_modulus_space ha
  have hMnot : ¬ 3 ∣ M := GNExcessCubicRealizedLargeModulusSpace_not_three_dvd hMspace
  have hMcop : Nat.Coprime 3 M :=
    (GNExcessCubicRealizedLargeModulusSpace_coprime_three hMspace).symm
  have hMEq : M * S = a ^ 2 + 3 * a + 3 := hEq
  constructor
  · intro hS
    have hF : 3 ∣ a ^ 2 + 3 * a + 3 := by
      rw [← hMEq]
      exact dvd_mul_of_dvd_right hS M
    exact (three_dvd_cubicQuadratic_iff a).mp hF
  · intro ha3
    have hF : 3 ∣ a ^ 2 + 3 * a + 3 :=
      (three_dvd_cubicQuadratic_iff a).mpr ha3
    have hMS : 3 ∣ M * S := by simpa [hMEq] using hF
    exact hMcop.dvd_of_dvd_mul_left hMS

theorem GNExcessCubicRealizedLargeModulusShellWitness_not_nine_dvd_complement
    {X D a : ℕ} (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ¬ 9 ∣ GNExcessCubicComplement a := by
  obtain ⟨_, _, _, _, _, hEq, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha
  intro hS
  apply not_nine_dvd_GN_three_one a
  rw [← hEq]
  exact dvd_mul_of_dvd_right hS _

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_three_dvd_pellParameter_iff
    {X D M S : ℕ}
    (hMS : (M, S) ∈ GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    3 ∣ oddPart M * S ↔ 3 ∣ S := by
  obtain ⟨a, ha, hpair, _, _, _, _, _, _, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hMspace0 := threeSector_shell_witness_modulus_space ha
  have hMfull : GNExcessCubicFullRepeatedModulus a = M := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
  have hMspace : M ∈ GNExcessCubicRealizedLargeModulusSpace X := by
    simpa [hMfull] using hMspace0
  have hrd : oddPart M ∣ M := by
    exact oddPart_dvd_of_squarefull (Nat.ne_of_gt
      (GNExcessCubicRealizedLargeModulusSpace_pos hMspace))
      (GNExcessCubicRealizedLargeModulusSpace_squarefull hMspace)
  have hodd : ¬ 3 ∣ oddPart M := by
    intro h
    exact GNExcessCubicRealizedLargeModulusSpace_not_three_dvd hMspace
      (dvd_trans h hrd)
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact False.elim (hodd h)
    · exact h
  · intro h
    exact dvd_mul_of_dvd_right h _

theorem GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_pellParameter_iff
    {X D a : ℕ} (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    3 ∣ oddPart (GNExcessCubicFullRepeatedModulus a) *
      GNExcessCubicComplement a ↔ 3 ∣ a := by
  rw [GNExcessCubicRealizedLargeModulusShellIncidencePair_three_dvd_pellParameter_iff
    (Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
  exact GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_complement_iff ha

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_eq_one_or_three
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    Nat.gcd (2 * a + 3) (oddPart M * S) = 1 ∨
      Nat.gcd (2 * a + 3) (oddPart M * S) = 3 := by
  let g := Nat.gcd (2 * a + 3) (oddPart M * S)
  have hgdiv := GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_dvd_three ha hpair
  have hMS : (M, S) ∈ GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨a, ha, hpair⟩
  obtain ⟨_, _, _, _, _, _, _, _, hSpos, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hrop : 0 < oddPart M := by
    obtain ⟨hdecomp, _, _⟩ :=
      GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
    have hMpos : 0 < M := by omega
    by_contra h
    have h0 : oddPart M = 0 := Nat.eq_zero_of_not_pos h
    rw [h0] at hdecomp
    simp at hdecomp
    omega
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hrop hSpos)
  rcases (Nat.dvd_prime Nat.prime_three).mp hgdiv with hg1 | hg3
  · exact Or.inl hg1
  · exact Or.inr hg3

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_eq_three_iff_three_dvd_witness
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    Nat.gcd (2 * a + 3) (oddPart M * S) = 3 ↔ 3 ∣ a := by
  let g := Nat.gcd (2 * a + 3) (oddPart M * S)
  have hclass := GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_eq_one_or_three ha hpair
  have hgY : g ∣ 2 * a + 3 := Nat.gcd_dvd_left _ _
  have hgT : g ∣ oddPart M * S := Nat.gcd_dvd_right _ _
  constructor
  · intro h
    have h3y : 3 ∣ 2 * a + 3 := by simpa [g, h] using hgY
    exact (three_dvd_pellY_iff a).mp h3y
  · intro ha3
    have h3y : 3 ∣ 2 * a + 3 := (three_dvd_pellY_iff a).mpr ha3
    have hM : GNExcessCubicFullRepeatedModulus a = M := by
      simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
    have hS : GNExcessCubicComplement a = S := by
      simpa [GNExcessCubicIncidencePair] using congrArg Prod.snd hpair
    have h3T' :=
      (GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_pellParameter_iff ha).mpr ha3
    rw [hM, hS] at h3T'
    have h3T : 3 ∣ oddPart M * S := h3T'
    have hg3 : 3 ∣ g := Nat.dvd_gcd h3y h3T
    rcases hclass with h1 | h3
    · simp [g, h1] at hg3
    · exact h3

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_eq_three_iff_three_dvd_complement
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    Nat.gcd (2 * a + 3) (oddPart M * S) = 3 ↔ 3 ∣ S := by
  have hS : GNExcessCubicComplement a = S := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.snd hpair
  have hcomp : 3 ∣ GNExcessCubicComplement a ↔ 3 ∣ S := by simp [hS]
  exact (GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_eq_three_iff_three_dvd_witness
    ha hpair).trans ((GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_complement_iff ha).symm.trans hcomp)

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_eq_three_iff_three_dvd_pellParameter
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    Nat.gcd (2 * a + 3) (oddPart M * S) = 3 ↔ 3 ∣ oddPart M * S := by
  have hM : GNExcessCubicFullRepeatedModulus a = M := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
  have hS : GNExcessCubicComplement a = S := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.snd hpair
  have hT : oddPart (GNExcessCubicFullRepeatedModulus a) *
      GNExcessCubicComplement a = oddPart M * S := by rw [hM, hS]
  have hTiff : 3 ∣ oddPart (GNExcessCubicFullRepeatedModulus a) *
      GNExcessCubicComplement a ↔ 3 ∣ oddPart M * S := by simp [hT]
  exact (GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_eq_three_iff_three_dvd_witness
    ha hpair).trans ((GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_pellParameter_iff ha).symm.trans hTiff)

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_primitive_packet
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T)
    (ha3 : ¬ 3 ∣ a) :
    ¬ 3 ∣ 2 * a + 3 ∧ ¬ 3 ∣ T ∧
    Nat.gcd (2 * a + 3) T = 1 ∧ Nat.Coprime (2 * a + 3) T ∧
    (2 * a + 3) ^ 2 + 3 =
      4 * T * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 ∧
    Nat.Coprime (2 * a + 3)
      (evenPart (GNExcessCubicFullRepeatedModulus a)) ∧
    Squarefree T := by
  have hF := mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp ha
  have hpair : GNExcessCubicIncidencePair a =
      (GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a) := rfl
  have hgclass :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_eq_one_or_three
      hF.1 hpair
  have hga : Nat.gcd (2 * a + 3) T = 1 ∨ Nat.gcd (2 * a + 3) T = 3 := by
    simpa [hF.2] using hgclass
  have h3T : ¬ 3 ∣ T := by
    intro h
    have h3T' : 3 ∣ oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a := by simpa [hF.2] using h
    exact ha3 ((GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_pellParameter_iff
      hF.1).mp h3T')
  have hg1 : Nat.gcd (2 * a + 3) T = 1 := by
    rcases hga with h | h
    · exact h
    · exfalso
      apply h3T
      have hg3 : 3 ∣ Nat.gcd (2 * a + 3) T := by
        simpa only [h] using (dvd_refl 3 : 3 ∣ 3)
      exact dvd_trans hg3 (Nat.gcd_dvd_right _ _)
  have hcop : Nat.Coprime (2 * a + 3) T :=
    Nat.coprime_iff_gcd_eq_one.mpr hg1
  have hp := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet ha
  exact ⟨fun h => ha3 ((three_dvd_pellY_iff a).mp h), h3T, hg1, hcop,
    (GNExcessCubicRealizedLargeModulusShellPellParameterFiber_equation ha), hp.2.2.2.1,
    GNExcessCubicRealizedLargeModulusShellPellParameterSpace_squarefree
      (by exact Finset.mem_image.mpr ⟨(GNExcessCubicFullRepeatedModulus a,
        GNExcessCubicComplement a),
        Finset.mem_image.mpr ⟨a, hF.1, rfl⟩, hF.2⟩)⟩

noncomputable def GNExcessCubicThreeSectorY (a : ℕ) : ℕ := (2 * a + 3) / 3

noncomputable def GNExcessCubicThreeSectorComplement (a : ℕ) : ℕ :=
  GNExcessCubicComplement a / 3

noncomputable def GNExcessCubicThreeSectorPellParameter (T : ℕ) : ℕ := T / 3

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_reconstruction
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T)
    (ha3 : 3 ∣ a) :
    2 * a + 3 = 3 * GNExcessCubicThreeSectorY a ∧
    GNExcessCubicComplement a =
      3 * GNExcessCubicThreeSectorComplement a ∧
    T = 3 * GNExcessCubicThreeSectorPellParameter T ∧
    ¬ 3 ∣ GNExcessCubicThreeSectorComplement a ∧
    ¬ 3 ∣ GNExcessCubicThreeSectorPellParameter T := by
  have hF := mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp ha
  have hS3 : 3 ∣ GNExcessCubicComplement a :=
    (GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_complement_iff hF.1).mpr ha3
  have hT3 : 3 ∣ T := by
    have hparam := (GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_pellParameter_iff
      hF.1).mpr ha3
    simpa [hF.2] using hparam
  have hy3 : 3 ∣ 2 * a + 3 := (three_dvd_pellY_iff a).mpr ha3
  have hy : 2 * a + 3 = 3 * GNExcessCubicThreeSectorY a := by
    simpa [GNExcessCubicThreeSectorY, Nat.mul_comm] using (Nat.div_mul_cancel hy3).symm
  have hS : GNExcessCubicComplement a =
      3 * GNExcessCubicThreeSectorComplement a := by
    simpa [GNExcessCubicThreeSectorComplement, Nat.mul_comm] using (Nat.div_mul_cancel hS3).symm
  have hT : T = 3 * GNExcessCubicThreeSectorPellParameter T := by
    simpa [GNExcessCubicThreeSectorPellParameter, Nat.mul_comm] using (Nat.div_mul_cancel hT3).symm
  have hnotS3 : ¬ 3 ∣ GNExcessCubicThreeSectorComplement a := by
    intro h
    obtain ⟨k, hk⟩ := h
    apply GNExcessCubicRealizedLargeModulusShellWitness_not_nine_dvd_complement hF.1
    rw [hS]
    refine ⟨k, ?_⟩
    omega
  have hnotT3 : ¬ 3 ∣ GNExcessCubicThreeSectorPellParameter T := by
    intro h
    obtain ⟨k, hk⟩ := h
    have h9 : 9 ∣ T := by
      rw [hT]
      refine ⟨k, ?_⟩
      omega
    have hSqT := GNExcessCubicRealizedLargeModulusShellPellParameterSpace_squarefree
      (by exact Finset.mem_image.mpr ⟨(GNExcessCubicFullRepeatedModulus a,
        GNExcessCubicComplement a), Finset.mem_image.mpr ⟨a, hF.1, rfl⟩, hF.2⟩)
    have hu := hSqT 3 (by simpa [pow_two] using h9)
    exact (by norm_num : ¬ IsUnit (3 : ℕ)) hu
  exact ⟨hy, hS, hT, hnotS3, hnotT3⟩

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_equation
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T)
    (ha3 : 3 ∣ a) :
    3 * (GNExcessCubicThreeSectorY a) ^ 2 + 1 =
      4 * (GNExcessCubicThreeSectorPellParameter T) *
        (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
  have hrec := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_reconstruction
    ha ha3
  have hEq := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_equation ha
  rw [hrec.1, hrec.2.2.1] at hEq
  have hEq' : 9 * (GNExcessCubicThreeSectorY a) ^ 2 + 3 =
      12 * (GNExcessCubicThreeSectorPellParameter T) *
        (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
    nlinarith [hEq]
  have hmul : 3 * (3 * (GNExcessCubicThreeSectorY a) ^ 2 + 1) =
      3 * (4 * (GNExcessCubicThreeSectorPellParameter T) *
        (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2) := by
    nlinarith [hEq']
  omega

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_coprime
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T)
    (ha3 : 3 ∣ a) :
    Nat.Coprime (GNExcessCubicThreeSectorY a)
      (GNExcessCubicThreeSectorPellParameter T) ∧
    Nat.Coprime (GNExcessCubicThreeSectorY a)
      (evenPart (GNExcessCubicFullRepeatedModulus a)) := by
  have hF := mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp ha
  have hrec := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_reconstruction
    ha ha3
  have hg := GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_eq_three_iff_three_dvd_witness
    hF.1 (show GNExcessCubicIncidencePair a =
      (GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a) from rfl)
  have hga : Nat.gcd (2 * a + 3)
      (oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a) = 3 := hg.mpr ha3
  have hgy : Nat.gcd (GNExcessCubicThreeSectorY a)
      (GNExcessCubicThreeSectorPellParameter T) = 1 := by
    rw [hrec.1, hF.2, hrec.2.2.1] at hga
    have hmul : Nat.gcd (3 * GNExcessCubicThreeSectorY a)
        (3 * GNExcessCubicThreeSectorPellParameter T) = 3 := by
      exact hga
    rw [Nat.gcd_mul_left] at hmul
    omega
  have hcopd := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet ha
  exact ⟨Nat.coprime_iff_gcd_eq_one.mpr hgy,
    Nat.Coprime.of_dvd_left (by
      refine ⟨3, ?_⟩
      simpa [Nat.mul_comm] using hrec.1) hcopd.2.2.2.1⟩

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_cases
    {X D T a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T) :
    (¬ 3 ∣ a ∧ Nat.Coprime (2 * a + 3) T ∧
      (2 * a + 3) ^ 2 + 3 =
        4 * T * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2) ∨
    (∃ y3 T3 : ℕ, 3 ∣ a ∧
      2 * a + 3 = 3 * y3 ∧ T = 3 * T3 ∧
      Nat.Coprime y3 T3 ∧
      3 * y3 ^ 2 + 1 =
        4 * T3 * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2) := by
  by_cases ha3 : 3 ∣ a
  · have hrec := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_reconstruction
      ha ha3
    have hcop := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_coprime
      ha ha3
    refine Or.inr ⟨GNExcessCubicThreeSectorY a,
      GNExcessCubicThreeSectorPellParameter T, ha3, hrec.1, hrec.2.2.1, hcop.1, ?_⟩
    exact GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_equation ha ha3
  · have hp := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_primitive_packet
      ha ha3
    exact Or.inl ⟨ha3, hp.2.2.2.1, hp.2.2.2.2.1⟩

end DkMath.ABC
