/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicPellParameterIncidence

#print "file: DkMath.ABC.GNExcessCubicPrimitivePell"

/-!
# Primitive support packet for the cubic Pell coordinates

This module freezes divisibility, prime-support, coprimality, and square-root
conditions for the exact finite shell coordinates from LUNA-014.  It contains
no count, density, or Pell-solution estimate.
-/

namespace DkMath.ABC

/-! ## Divisibility hierarchy -/

theorem GNExcessCubicSquarefulQuotient_dvd_evenPart
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    GNExcessCubicSquarefulQuotient M ∣ evenPart M := by
  have hrec := evenPart_eq_oddPart_mul_GNExcessCubicSquarefulQuotient hM hfull
  simpa only [hrec, mul_comm] using
    (dvd_mul_right (GNExcessCubicSquarefulQuotient M) (oddPart M))

theorem evenPart_dvd_of_squarefull
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    evenPart M ∣ M := by
  obtain ⟨hdecomp, _, _⟩ := squareful_oddEven_packet hM hfull
  have hdiv : evenPart M ∣ oddPart M * (evenPart M) ^ 2 :=
    dvd_mul_of_dvd_right (dvd_pow_self (evenPart M)
      (by decide : (2 : ℕ) ≠ 0)) (oddPart M)
  calc
    evenPart M ∣ oddPart M * (evenPart M) ^ 2 := hdiv
    _ = M := hdecomp.symm

theorem oddPart_dvd_of_squarefull
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    oddPart M ∣ M := by
  obtain ⟨hdecomp, _, _⟩ := squareful_oddEven_packet hM hfull
  have hdiv : oddPart M ∣ oddPart M * (evenPart M) ^ 2 :=
    dvd_mul_right (oddPart M) ((evenPart M) ^ 2)
  calc
    oddPart M ∣ oddPart M * (evenPart M) ^ 2 := hdiv
    _ = M := hdecomp.symm

theorem GNExcessCubicSquarefulQuotient_dvd_of_squarefull
    {M : ℕ} (hM : M ≠ 0) (hfull : squarefull M) :
    GNExcessCubicSquarefulQuotient M ∣ M := by
  exact dvd_trans (GNExcessCubicSquarefulQuotient_dvd_evenPart hM hfull)
    (evenPart_dvd_of_squarefull hM hfull)

/-! ## Prime support of the three squareful coordinates -/

theorem GNExcessCubicRealizedLargeModulusSpace_oddPart_prime_mod_three_eq_one
    {X M q : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X)
    (hq : Nat.Prime q) (hqdvd : q ∣ oddPart M) :
    q % 3 = 1 := by
  exact GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one hM hq
    (dvd_trans hqdvd (oddPart_dvd_of_squarefull
      (Nat.ne_of_gt (GNExcessCubicRealizedLargeModulusSpace_pos hM))
      (GNExcessCubicRealizedLargeModulusSpace_squarefull hM)))

theorem GNExcessCubicRealizedLargeModulusSpace_evenPart_prime_mod_three_eq_one
    {X M q : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X)
    (hq : Nat.Prime q) (hqdvd : q ∣ evenPart M) :
    q % 3 = 1 := by
  exact GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one hM hq
    (dvd_trans hqdvd (evenPart_dvd_of_squarefull
      (Nat.ne_of_gt (GNExcessCubicRealizedLargeModulusSpace_pos hM))
      (GNExcessCubicRealizedLargeModulusSpace_squarefull hM)))

theorem GNExcessCubicRealizedLargeModulusSpace_squarefulQuotient_prime_mod_three_eq_one
    {X M q : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X)
    (hq : Nat.Prime q)
    (hqdvd : q ∣ GNExcessCubicSquarefulQuotient M) :
    q % 3 = 1 := by
  exact GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one hM hq
    (dvd_trans hqdvd (GNExcessCubicSquarefulQuotient_dvd_of_squarefull
      (Nat.ne_of_gt (GNExcessCubicRealizedLargeModulusSpace_pos hM))
      (GNExcessCubicRealizedLargeModulusSpace_squarefull hM)))

/-! ## The Pell y-coordinate and the repeated modulus -/

private theorem shell_witness_modulus_space
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    GNExcessCubicFullRepeatedModulus a ∈
      GNExcessCubicRealizedLargeModulusSpace X := by
  have hMsh : GNExcessCubicFullRepeatedModulus a ∈
      GNExcessCubicRealizedLargeModulusShell X D := by
    rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell X D]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact GNExcessCubicRealizedLargeModulusShell_subset X D hMsh

theorem GNExcessCubicRealizedLargeModulusShellWitness_coprime_pellY_modulus
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    Nat.Coprime (2 * a + 3) (GNExcessCubicFullRepeatedModulus a) := by
  by_contra hnot
  obtain ⟨q, hq, hqy, hqM⟩ :=
    (Nat.Prime.not_coprime_iff_dvd.mp hnot)
  have hMspace := shell_witness_modulus_space ha
  have hqmod := GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one
    hMspace hq hqM
  obtain ⟨ha1, haX, hD, h2D, hlarge, hEq, hSq, hCop, hSX⟩ :=
    GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha
  have hqF : q ∣ a ^ 2 + 3 * a + 3 := by
    rw [← hEq]
    exact dvd_mul_of_dvd_left hqM _
  have hqSum : q ∣ (2 * a + 3) ^ 2 + 3 := by
    have hq4F : q ∣ 4 * (a ^ 2 + 3 * a + 3) :=
      dvd_mul_of_dvd_right hqF 4
    rw [cubicQuadratic_discriminant_identity] at hq4F
    exact hq4F
  have hqY2 : q ∣ (2 * a + 3) ^ 2 := dvd_pow hqy (by decide)
  have hq3 : q ∣ 3 := by
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hqSum hqY2
  have hqeq : q = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hq3 with hqone | hqthree
    · exact False.elim (hq.ne_one hqone)
    · exact hqthree
  subst q
  norm_num at hqmod

theorem GNExcessCubicRealizedLargeModulusShellWitness_pellY_coordinate_coprime_packet
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    Nat.Coprime (2 * a + 3) (oddPart (GNExcessCubicFullRepeatedModulus a)) ∧
    Nat.Coprime (2 * a + 3) (evenPart (GNExcessCubicFullRepeatedModulus a)) ∧
    Nat.Coprime (2 * a + 3)
      (GNExcessCubicSquarefulQuotient (GNExcessCubicFullRepeatedModulus a)) := by
  have hcop := GNExcessCubicRealizedLargeModulusShellWitness_coprime_pellY_modulus ha
  have hMspace := shell_witness_modulus_space ha
  have hfull := GNExcessCubicRealizedLargeModulusSpace_squarefull hMspace
  have hMpos := GNExcessCubicRealizedLargeModulusSpace_pos hMspace
  exact ⟨Nat.Coprime.of_dvd_right
      (oddPart_dvd_of_squarefull (Nat.ne_of_gt hMpos) hfull) hcop,
    Nat.Coprime.of_dvd_right
      (evenPart_dvd_of_squarefull (Nat.ne_of_gt hMpos) hfull) hcop,
    Nat.Coprime.of_dvd_right
      (GNExcessCubicSquarefulQuotient_dvd_of_squarefull
        (Nat.ne_of_gt hMpos) hfull) hcop⟩

/-! ## Complement coprimality -/

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_squareCube_coprime_packet
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    Nat.Coprime (evenPart M) S ∧
      Nat.Coprime (GNExcessCubicSquarefulQuotient M) S := by
  obtain ⟨_, _, hrd, _, hCop, _, _, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
  obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop', hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hMpos : 0 < M := by omega
  have hMne : M ≠ 0 := Nat.ne_of_gt hMpos
  have hMfull : GNExcessCubicFullRepeatedModulus a = M := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
  have hfullFull := GNExcessCubicRealizedLargeModulusSpace_squarefull
    (shell_witness_modulus_space ha)
  have hfull : squarefull M := by simpa [hMfull] using hfullFull
  have hdM := evenPart_dvd_of_squarefull hMne hfull
  exact ⟨Nat.Coprime.of_dvd_left hdM hCop,
    Nat.Coprime.of_dvd_left
      (GNExcessCubicSquarefulQuotient_dvd_of_squarefull hMne hfull) hCop⟩

/-! ## The primitive gcd boundary -/

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_dvd_three
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    Nat.gcd (2 * a + 3) (oddPart M * S) ∣ 3 := by
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D := by
    exact Finset.mem_image.mpr ⟨a, ha, hpair⟩
  obtain ⟨_, _, hrd, _, _, _, _, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
  obtain ⟨a', ha', hpair', ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have haeq : a' = a := GNExcessCubicIncidencePair_injective
    (hpair'.trans hpair.symm)
  subst a'
  let g := Nat.gcd (2 * a + 3) (oddPart M * S)
  have hgY : g ∣ 2 * a + 3 := Nat.gcd_dvd_left _ _
  have hgT : g ∣ oddPart M * S := Nat.gcd_dvd_right _ _
  have hMdiv : oddPart M ∣ M := by
    refine ⟨(evenPart M) ^ 2, ?_⟩
    exact (GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS).1
  have hTdiv : oddPart M * S ∣ M * S :=
    Nat.mul_dvd_mul_right hMdiv S
  have hgMS : g ∣ M * S := dvd_trans hgT hTdiv
  have hgF : g ∣ a ^ 2 + 3 * a + 3 := by
    rw [← hEq]
    exact hgMS
  have hgSum : g ∣ (2 * a + 3) ^ 2 + 3 := by
    have hg4F : g ∣ 4 * (a ^ 2 + 3 * a + 3) :=
      dvd_mul_of_dvd_right hgF 4
    rw [cubicQuadratic_discriminant_identity] at hg4F
    exact hg4F
  have hgY2 : g ∣ (2 * a + 3) ^ 2 := dvd_pow hgY (by decide)
  simpa [g, Nat.add_sub_cancel_left] using Nat.dvd_sub hgSum hgY2

/-! ## Square divisibility and local prime packets -/

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_sq_dvd_pellValue
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    (evenPart M) ^ 2 ∣ (2 * a + 3) ^ 2 + 3 := by
  have hpell := GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity
    ha hpair
  calc
    (evenPart M) ^ 2 ∣
        4 * (oddPart M * S) * (evenPart M) ^ 2 :=
      dvd_mul_left _ _
    _ = (2 * a + 3) ^ 2 + 3 := hpell.symm

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefulQuotient_sq_dvd_pellValue
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    (GNExcessCubicSquarefulQuotient M) ^ 2 ∣ (2 * a + 3) ^ 2 + 3 := by
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D := by
    exact Finset.mem_image.mpr ⟨a, ha, hpair⟩
  have hqdiv := GNExcessCubicSquarefulQuotient_dvd_evenPart
    (by
      obtain ⟨a', ha', hpair', ha1', haX', hD', h2D', hlarge', hSpos', hSX',
          hSq', hCop', hEq'⟩ :=
        GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
      have hMpos : 0 < M := by omega
      exact Nat.ne_of_gt hMpos)
    (by
      obtain ⟨a', ha', hpair', ha1', haX', hD', h2D', hlarge', hSpos', hSX',
          hSq', hCop', hEq'⟩ :=
        GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
      have hfull' := GNExcessCubicRealizedLargeModulusSpace_squarefull
        (shell_witness_modulus_space ha')
      have hMfull : GNExcessCubicFullRepeatedModulus a' = M := by
        simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair'
      simpa [hMfull] using hfull')
  exact dvd_trans (pow_dvd_pow_of_dvd hqdiv 2)
    (GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_sq_dvd_pellValue
      ha hpair)

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_prime_packet
    {X D M S q : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D)
    (hq : Nat.Prime q) (hqdvd : q ∣ evenPart M) :
    ∃ a,
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
      GNExcessCubicIncidencePair a = (M, S) ∧
      q % 3 = 1 ∧
      q ^ 2 ∣ (2 * a + 3) ^ 2 + 3 := by
  obtain ⟨a, ha, hpair, _, _, _, _, _, _, _, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hMspace := shell_witness_modulus_space ha
  have hMfull : GNExcessCubicFullRepeatedModulus a = M := by
    simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
  have hqdvd' : q ∣ evenPart (GNExcessCubicFullRepeatedModulus a) := by
    simpa [hMfull] using hqdvd
  have hmod := GNExcessCubicRealizedLargeModulusSpace_evenPart_prime_mod_three_eq_one
    hMspace hq hqdvd'
  have hsq : q ^ 2 ∣ (evenPart M) ^ 2 := by
    simpa [hMfull] using pow_dvd_pow_of_dvd hqdvd' 2
  have hpell := GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_sq_dvd_pellValue
    ha hpair
  exact ⟨a, ha, hpair, hmod, dvd_trans hsq hpell⟩

theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefulQuotient_prime_packet
    {X D M S q : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D)
    (hq : Nat.Prime q)
    (hqdvd : q ∣ GNExcessCubicSquarefulQuotient M) :
    ∃ a,
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
      GNExcessCubicIncidencePair a = (M, S) ∧
      q % 3 = 1 ∧
      q ^ 2 ∣ (2 * a + 3) ^ 2 + 3 := by
  have hqeven := dvd_trans hqdvd
    (GNExcessCubicSquarefulQuotient_dvd_evenPart
      (by
        obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
            hSq, hCop, hEq⟩ :=
          GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
        have hMpos : 0 < M := by omega
        exact Nat.ne_of_gt hMpos)
      (by
        obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
            hSq, hCop, hEq⟩ :=
          GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
        have hfull' := GNExcessCubicRealizedLargeModulusSpace_squarefull
          (shell_witness_modulus_space ha)
        have hMfull : GNExcessCubicFullRepeatedModulus a = M := by
          simpa [GNExcessCubicIncidencePair] using congrArg Prod.fst hpair
        simpa [hMfull] using hfull'))
  exact GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_prime_packet
    hMS hq hqeven

/-! ## Fixed-parameter primitive conic packet -/

theorem GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet
    {X D T a : ℕ}
    (ha : a ∈
      GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T) :
    0 < evenPart (GNExcessCubicFullRepeatedModulus a) ∧
    0 < GNExcessCubicSquarefulQuotient
      (GNExcessCubicFullRepeatedModulus a) ∧
    (2 * a + 3) ^ 2 + 3 =
      4 * T * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 ∧
    Nat.Coprime (2 * a + 3)
      (evenPart (GNExcessCubicFullRepeatedModulus a)) ∧
    Nat.Coprime (2 * a + 3)
      (GNExcessCubicSquarefulQuotient
        (GNExcessCubicFullRepeatedModulus a)) ∧
    Nat.gcd (2 * a + 3)
      (oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a) ∣ 3 ∧
    (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 ∣
      (2 * a + 3) ^ 2 + 3 ∧
    ∀ q, Nat.Prime q →
      q ∣ evenPart (GNExcessCubicFullRepeatedModulus a) →
      q % 3 = 1 ∧
        q ^ 2 ∣ (2 * a + 3) ^ 2 + 3 := by
  have hF :=
    mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp ha
  let M := GNExcessCubicFullRepeatedModulus a
  let S := GNExcessCubicComplement a
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D := by
    exact Finset.mem_image.mpr ⟨a, hF.1, rfl⟩
  have hMspace := shell_witness_modulus_space hF.1
  have hpack := GNExcessCubicRealizedLargeModulusSpace_squareCube_packet hMspace
  have hrec := evenPart_eq_oddPart_mul_GNExcessCubicSquarefulQuotient
    (Nat.ne_of_gt hpack.1) hpack.2.1
  have hdpos : 0 < evenPart M := by
    rw [hrec]
    exact Nat.mul_pos hpack.2.2.2.1 hpack.2.2.2.2.1
  have hcop := GNExcessCubicRealizedLargeModulusShellWitness_pellY_coordinate_coprime_packet
    hF.1
  have hpell := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_equation ha
  have hgcd := GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_dvd_three
    hF.1 (show GNExcessCubicIncidencePair a = (M, S) from rfl)
  have hdvd := GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_sq_dvd_pellValue
    hF.1 (show GNExcessCubicIncidencePair a = (M, S) from rfl)
  refine ⟨hdpos, hpack.2.2.2.2.1, ?_, hcop.2.1, hcop.2.2,
    ?_, ?_, ?_⟩
  · exact hpell
  · simpa [M, S] using hgcd
  · simpa [M, S] using hdvd
  · intro q hq hqd
    have hmod := GNExcessCubicRealizedLargeModulusSpace_evenPart_prime_mod_three_eq_one
      hMspace hq hqd
    have hsq : q ^ 2 ∣ (evenPart M) ^ 2 := pow_dvd_pow_of_dvd hqd 2
    exact ⟨hmod, dvd_trans hsq hdvd⟩

end DkMath.ABC
