/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredPacketTriangle

#print "file: DkMath.NumberTheory.Legendre.CenteredPacketDiamond"

/-!
## CenteredPacketDiamond

The fourth seat `6 * k + 2` extends the L025 three-seat configuration by
one consecutive point.  Five complete-point edges remain coprime, while
the A/D edge has an explicit common prime `2`.  The API records this
exceptional collision and the resulting full-cover witness package without
introducing graph terminology or claiming a contradiction.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive

/-! ### PRIM-L026.1: fourth-seat shell membership -/

/-- The fourth diamond seat is in the shell anchored at `4 * k`. -/
theorem squareOffset_centeredPacketDiamond_D
    {k : ℕ} (hk : 0 < k) :
    SquareOffset (4 * k) (6 * k + 2) := by
  dsimp [SquareOffset]
  omega

/-! ### PRIM-L026.2: consecutive pair C/D -/

/-- The complete points at the consecutive seats C and D are coprime. -/
theorem coprime_centeredPacketDiamond_CD
    (k : ℕ) :
    Nat.Coprime ((4 * k) ^ 2 + (6 * k + 1))
      ((4 * k) ^ 2 + (6 * k + 2)) := by
  have hcop : Nat.Coprime ((4 * k) ^ 2 + (6 * k + 1))
      (((4 * k) ^ 2 + (6 * k + 1)) + 1) := by
    exact Nat.coprime_self_add_right.mpr (by simp)
  have hpoint :
      (4 * k) ^ 2 + (6 * k + 2) =
        ((4 * k) ^ 2 + (6 * k + 1)) + 1 := by
    omega
  rw [hpoint]
  exact hcop

/-! ### PRIM-L026.3: prime-gap pair B/D -/

/-- The prime gap `4 * k + 1` does not divide the B point. -/
theorem not_four_mul_k_add_one_dvd_centeredPacketTriangle_B
    {k : ℕ} (hk : 0 < k) :
    ¬ (4 * k + 1) ∣ ((4 * k) ^ 2 + (2 * k + 1)) := by
  intro hdiv
  have hdouble : 4 * k + 1 ∣
      2 * ((4 * k) ^ 2 + (2 * k + 1)) := by
    exact dvd_mul_of_dvd_right hdiv 2
  have hsum : 4 * k + 1 ∣
      2 * ((4 * k) ^ 2 + (2 * k + 1)) + (4 * k + 1) := by
    exact dvd_add hdouble (dvd_refl _)
  have hidentity :
      2 * ((4 * k) ^ 2 + (2 * k + 1)) + (4 * k + 1) =
        (4 * k + 1) * (8 * k) + 3 := by
    ring
  rw [hidentity] at hsum
  have hthree : 4 * k + 1 ∣ 3 :=
    (Nat.dvd_add_iff_right
      (dvd_mul_right (4 * k + 1) (8 * k))).mpr hsum
  have hle : 4 * k + 1 ≤ 3 := Nat.le_of_dvd (by norm_num) hthree
  omega

/-- The complete points at the prime-gap seats B and D are coprime. -/
theorem coprime_centeredPacketDiamond_BD
    {k : ℕ}
    (hk : 0 < k)
    (hprime : Nat.Prime (4 * k + 1)) :
    Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
      ((4 * k) ^ 2 + (6 * k + 2)) := by
  have hnot : ¬ (4 * k + 1) ∣ ((4 * k) ^ 2 + (2 * k + 1)) :=
    not_four_mul_k_add_one_dvd_centeredPacketTriangle_B hk
  have hcopGap : Nat.Coprime (4 * k + 1)
      ((4 * k) ^ 2 + (2 * k + 1)) :=
    hprime.coprime_iff_not_dvd.mpr hnot
  have hpoint :
      (4 * k) ^ 2 + (6 * k + 2) =
        ((4 * k) ^ 2 + (2 * k + 1)) + (4 * k + 1) := by
    ring
  rw [hpoint]
  exact Nat.coprime_self_add_right.mpr hcopGap.symm

/-! ### PRIM-L026.4: explicit A/D false beam -/

/-- Prime `2` is an old-prime support direction for the A seat. -/
theorem two_mem_centeredPacketDiamond_support_A
    {k : ℕ} (hk : 0 < k) :
    2 ∈ squareOffsetPrimeSupport (4 * k) (2 * k) := by
  apply mem_squareOffsetPrimeSupport.mpr
  refine ⟨Nat.prime_two, ?_, ?_⟩
  · omega
  · refine ⟨8 * k ^ 2 + k, ?_⟩
    ring

/-- Prime `2` is an old-prime support direction for the D seat. -/
theorem two_mem_centeredPacketDiamond_support_D
    {k : ℕ} (hk : 0 < k) :
    2 ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 2) := by
  apply mem_squareOffsetPrimeSupport.mpr
  refine ⟨Nat.prime_two, ?_, ?_⟩
  · omega
  · refine ⟨8 * k ^ 2 + 3 * k + 1, ?_⟩
    ring

/-- The A/D support Finsets are not disjoint: they share the prime `2`. -/
theorem not_disjoint_centeredPacketDiamond_support_AD
    {k : ℕ} (hk : 0 < k) :
    ¬ Disjoint
      (squareOffsetPrimeSupport (4 * k) (2 * k))
      (squareOffsetPrimeSupport (4 * k) (6 * k + 2)) := by
  intro hdisj
  exact (Finset.disjoint_left.mp hdisj)
    (two_mem_centeredPacketDiamond_support_A hk)
    (two_mem_centeredPacketDiamond_support_D hk)

/-! ### PRIM-L026.5: A/D common-support localization -/

/-- Any common A/D old-prime support direction is `2` or `3`. -/
theorem common_centeredPacketDiamond_support_AD_eq_two_or_three
    {k q : ℕ}
    (_hk : 0 < k)
    (hA : q ∈ squareOffsetPrimeSupport (4 * k) (2 * k))
    (hD : q ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 2)) :
    q = 2 ∨ q = 3 := by
  have hA' := mem_squareOffsetPrimeSupport.mp hA
  have hD' := mem_squareOffsetPrimeSupport.mp hD
  have hgap : q ∣ 4 * k + 2 := by
    have hpoint :
        (4 * k) ^ 2 + (6 * k + 2) =
          ((4 * k) ^ 2 + 2 * k) + (4 * k + 2) := by
      ring
    rw [hpoint] at hD'
    exact (Nat.dvd_add_iff_right hA'.2.2).mpr hD'.2.2
  have hgap' : q ∣ 2 * (2 * k + 1) := by
    have hgapEq : 4 * k + 2 = 2 * (2 * k + 1) := by
      ring
    rw [hgapEq] at hgap
    exact hgap
  rcases (Nat.Prime.dvd_mul hA'.1).mp hgap' with hq2 | hqodd
  · left
    exact ((Nat.dvd_prime Nat.prime_two).mp hq2).resolve_left hA'.1.ne_one
  · have hsum : q ∣
        ((4 * k) ^ 2 + 2 * k) + 3 * (2 * k + 1) := by
      exact dvd_add hA'.2.2 (dvd_mul_of_dvd_right hqodd 3)
    have hidentity :
        ((4 * k) ^ 2 + 2 * k) + 3 * (2 * k + 1) =
          (2 * k + 1) * (8 * k) + 3 := by
      ring
    rw [hidentity] at hsum
    have hprod : q ∣ (2 * k + 1) * (8 * k) :=
      dvd_mul_of_dvd_left hqodd (8 * k)
    have hthree : q ∣ 3 :=
      (Nat.dvd_add_iff_right hprod).mpr hsum
    right
    exact ((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hthree).resolve_left
      hA'.1.ne_one

/-! ### PRIM-L026.6: five true edges and the exceptional edge -/

/-- The five good complete-point edges and the explicit A/D collision. -/
theorem centeredPacketDiamond_five_edges_and_AD_obstruction
    {k : ℕ}
    (hk : 0 < k)
    (hprime : Nat.Prime (4 * k + 1)) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (2 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (6 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (6 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 2)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 2)) ∧
      2 ∈ squareOffsetPrimeSupport (4 * k) (2 * k) ∧
      2 ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 2) := by
  exact ⟨coprime_centeredPacketTriangle_AB k,
    coprime_centeredPacketTriangle_BC k,
    coprime_centeredPacketTriangle_AC hprime,
    coprime_centeredPacketDiamond_CD k,
    coprime_centeredPacketDiamond_BD hk hprime,
    two_mem_centeredPacketDiamond_support_A hk,
    two_mem_centeredPacketDiamond_support_D hk⟩

/-! ### PRIM-L026.7: full-cover four-seat witness package -/

/-- Full cover gives four witnesses with exactly the five forced inequalities. -/
theorem exists_centeredPacketDiamond_four_witnesses_of_fullyCovered
    {k : ℕ}
    (hk : 0 < k)
    (hprime : Nat.Prime (4 * k + 1))
    (hfull : SquareOffsetsFullyCovered (4 * k)) :
    ∃ pA pB pC pD,
      pA ≠ pB ∧
      pA ≠ pC ∧
      pB ≠ pC ∧
      pB ≠ pD ∧
      pC ≠ pD ∧
      pA ∈ squareOffsetPrimeSupport (4 * k) (2 * k) ∧
      pB ∈ squareOffsetPrimeSupport (4 * k) (2 * k + 1) ∧
      pC ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 1) ∧
      pD ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 2) ∧
      (pA = pD → pA = 2 ∨ pA = 3) := by
  have hA := squareOffset_centeredPacketTriangle_A hk
  have hB := squareOffset_centeredPacketTriangle_B hk
  have hC := squareOffset_centeredPacketTriangle_C hk
  have hD := squareOffset_centeredPacketDiamond_D hk
  obtain ⟨pA, hpA⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hA)
  obtain ⟨pB, hpB⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hB)
  obtain ⟨pC, hpC⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hC)
  obtain ⟨pD, hpD⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hD)
  refine ⟨pA, pB, pC, pD, ?_, ?_, ?_, ?_, ?_, hpA, hpB, hpC, hpD, ?_⟩
  · intro h
    subst pB
    exact (Finset.disjoint_left.mp
      (disjoint_centeredPacketTriangle_support_AB k)) hpA hpB
  · intro h
    subst pC
    exact (Finset.disjoint_left.mp
      (disjoint_centeredPacketTriangle_support_AC hprime)) hpA hpC
  · intro h
    subst pC
    exact (Finset.disjoint_left.mp
      (disjoint_centeredPacketTriangle_support_BC k)) hpB hpC
  · intro h
    subst pD
    exact (Finset.disjoint_left.mp
      (disjoint_squareOffsetPrimeSupport_of_coprime_points
        (coprime_centeredPacketDiamond_BD hk hprime))) hpB hpD
  · intro h
    subst pD
    exact (Finset.disjoint_left.mp
      (disjoint_squareOffsetPrimeSupport_of_coprime_points
        (coprime_centeredPacketDiamond_CD k))) hpC hpD
  · intro h
    subst pD
    exact common_centeredPacketDiamond_support_AD_eq_two_or_three hk hpA hpD

end DkMath.NumberTheory.Legendre
