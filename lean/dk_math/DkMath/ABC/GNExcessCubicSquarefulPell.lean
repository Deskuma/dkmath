/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicComplementIncidence

/-!
# Squareful parity and Pell-shell coordinates

This module adds the exact odd/even factorization coordinates to the realized
cubic incidence pair.  A squareful modulus is written as `r * d^2`, with
`r = oddPart M` squarefree and `r ∣ d`; the canonical complement then gives
the negative-Pell shell equation.  No Pell solution count or shell estimate is
asserted.
-/

namespace DkMath.ABC

/-! ## Generic odd/even arithmetic -/

/-- The odd-exponent part of a natural number is squarefree. -/
theorem squarefree_oddPart (n : ℕ) : Squarefree (oddPart n) := by
  classical
  let s := n.factorization.support
  have hprod : Squarefree (s.prod (fun p => p)) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      have hpp : Nat.Prime p := (mem_support_factorization_iff.mp hp).2.1
      have hqq : Nat.Prime q := (mem_support_factorization_iff.mp hq).2.1
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes hpp hqq).mpr hpq)
    · intro p hp
      exact (Nat.prime_iff.mp (mem_support_factorization_iff.mp hp).2.1).irreducible.squarefree
  have hdvd : oddPart n ∣ s.prod (fun p => p) := by
    unfold oddPart
    exact Finset.prod_dvd_prod_of_dvd
      (fun p => p ^ (n.factorization p % 2)) (fun p => p) (by
        intro p hp
        have hmod : n.factorization p % 2 < 2 := Nat.mod_lt _ (by decide)
        have hd : p ^ (n.factorization p % 2) ∣ p ^ 1 :=
          pow_dvd_pow p (by omega)
        simpa using hd)
  exact hprod.squarefree_of_dvd (by simpa [s] using hdvd)

/-- A squareful nonzero number has its odd part dividing its even part. -/
theorem oddPart_dvd_evenPart_of_squarefull
    {n : ℕ} (hn : n ≠ 0) (hfull : squarefull n) :
    oddPart n ∣ evenPart n := by
  classical
  unfold oddPart evenPart
  apply Finset.prod_dvd_prod_of_dvd
    (fun p => p ^ (n.factorization p % 2))
    (fun p => p ^ (n.factorization p / 2))
  intro p hp
  have hpp : Nat.Prime p := (mem_support_factorization_iff.mp hp).2.1
  have hpdvd : p ∣ n := by
    exact (mem_support_factorization_iff.mp hp).2.2
  have hp2 : p ^ 2 ∣ n := hfull p hpp hpdvd
  have hv : 2 ≤ n.factorization p :=
    (hpp.pow_dvd_iff_le_factorization hn).mp hp2
  exact pow_dvd_pow p (by omega)

/-- Canonical squareful odd/even coordinates. -/
theorem squareful_oddEven_packet
    {n : ℕ} (hn : n ≠ 0) (hfull : squarefull n) :
    n = oddPart n * (evenPart n) ^ 2 ∧
      Squarefree (oddPart n) ∧
      oddPart n ∣ evenPart n := by
  refine ⟨decomp_oddPart_evenPart n hn, squarefree_oddPart n,
    oddPart_dvd_evenPart_of_squarefull hn hfull⟩

/-- A nonzero squareful number is a square times a squarefree cube. -/
theorem exists_sq_mul_cube_of_squarefull
    {n : ℕ} (hn : n ≠ 0) (hfull : squarefull n) :
    ∃ u r : ℕ, Squarefree r ∧ n = u ^ 2 * r ^ 3 := by
  obtain ⟨hdecomp, hsf, hrd⟩ := squareful_oddEven_packet hn hfull
  obtain ⟨u, hu⟩ := exists_eq_mul_right_of_dvd hrd
  refine ⟨u, oddPart n, hsf, ?_⟩
  calc
    n = oddPart n * (evenPart n) ^ 2 := hdecomp
    _ = u ^ 2 * (oddPart n) ^ 3 := by rw [hu]; ring

/-! ## Realized moduli and incidence-pair parity -/

/-- Every realized large cubic modulus is squareful in the generic predicate. -/
theorem GNExcessCubicRealizedLargeModulusSpace_squarefull
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    squarefull M := by
  intro q hq hqdvd
  exact GNExcessCubicRealizedLargeModulusSpace_prime_sq_dvd hM hq hqdvd

/-- Odd/even decomposition packet for a represented shell incidence pair. -/
theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    M = oddPart M * (evenPart M) ^ 2 ∧
      Squarefree (oddPart M) ∧
      oddPart M ∣ evenPart M ∧
      Squarefree S ∧ Nat.Coprime M S ∧
      Nat.Coprime (oddPart M) S ∧
      D ≤ M ∧ M < 2 * D ∧ X + 1 < M ∧
      1 ≤ S ∧ S ≤ X := by
  obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hMsh : M ∈ GNExcessCubicRealizedLargeModulusShell X D := by
    rw [← GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_fst_image_eq_shell X D]
    exact Finset.mem_image.mpr ⟨(M, S), hMS, rfl⟩
  have hMspace := GNExcessCubicRealizedLargeModulusShell_subset X D hMsh
  have hMpos := GNExcessCubicRealizedLargeModulusSpace_pos hMspace
  have hfull := GNExcessCubicRealizedLargeModulusSpace_squarefull hMspace
  have hpacket := squareful_oddEven_packet (Nat.ne_of_gt hMpos) hfull
  have hrdM : oddPart M ∣ M := by
    refine ⟨(evenPart M) ^ 2, ?_⟩
    exact hpacket.1
  have hcopr : Nat.Coprime (oddPart M) S :=
    Nat.Coprime.of_dvd_left hrdM hCop
  refine ⟨hpacket.1, hpacket.2.1, hpacket.2.2, hSq, hCop, hcopr,
    hD, h2D, hlarge, Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hSpos), hSX⟩

/-- The squarefree parameter `T = oddPart M * S` of a represented pair. -/
theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    Squarefree (oddPart M * S) := by
  have hp :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
  rcases hp with ⟨hdecomp, hrf, hrd, hSf, hMS, hRS, hD, h2D, hlarge,
    hS1, hSX⟩
  exact squarefree_mul_iff.mpr
    ⟨Nat.coprime_iff_isRelPrime.mp hRS, hrf, hSf⟩

/-! ## Negative-Pell shell identity -/

/-- The exact natural negative-Pell identity carried by a shell pair. -/
theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity
    {X D M S a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hpair : GNExcessCubicIncidencePair a = (M, S)) :
    (2 * a + 3) ^ 2 + 3 =
      4 * (oddPart M * S) * (evenPart M) ^ 2 := by
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D := by
    exact Finset.mem_image.mpr ⟨a, ha, hpair⟩
  obtain ⟨a', ha', hpair', _, _, _, _, hlarge, hSpos, hSX, hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have ha_eq : a' = a := GNExcessCubicIncidencePair_injective
    (hpair'.trans hpair.symm)
  subst a'
  have hMpos : 0 < M := by omega
  have hdecomp := decomp_oddPart_evenPart M (Nat.ne_of_gt hMpos)
  have hdisc := cubicQuadratic_discriminant_identity a
  have hEq' : M * S = a ^ 2 + 3 * a + 3 := hEq
  have hMSdecomp : M * S = (oddPart M * (evenPart M) ^ 2) * S := by
    exact congrArg (fun z : ℕ => z * S) hdecomp
  calc
    (2 * a + 3) ^ 2 + 3 = 4 * (a ^ 2 + 3 * a + 3) := hdisc.symm
    _ = 4 * (M * S) := by rw [hEq']
    _ = 4 * (oddPart M * (evenPart M) ^ 2 * S) :=
      congrArg (fun z : ℕ => 4 * z) hMSdecomp
    _ = 4 * (oddPart M * S) * (evenPart M) ^ 2 := by ring

/-! ## A reusable all-coordinate Pell packet -/

/-- All parity and Pell coordinates of a represented shell pair. -/
theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_packet
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    ∃ a y d r T : ℕ,
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
      GNExcessCubicIncidencePair a = (M, S) ∧
      y = 2 * a + 3 ∧ d = evenPart M ∧ r = oddPart M ∧
      T = r * S ∧ M = r * d ^ 2 ∧ Squarefree r ∧ r ∣ d ∧
      Squarefree T ∧ y ^ 2 + 3 = 4 * T * d ^ 2 ∧
      0 < y ∧ y % 2 = 1 ∧ 3 ≤ y ∧
      D ≤ M ∧ M < 2 * D ∧ X + 1 < M ∧ 1 ≤ S ∧ S ≤ X := by
  obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hpack :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS
  have hsfT :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter hMS
  have hpell :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity ha hpair
  refine ⟨a, 2 * a + 3, evenPart M, oddPart M, oddPart M * S,
    ha, hpair, rfl, rfl, rfl, rfl, hpack.1, hpack.2.1, hpack.2.2.1,
    hsfT, ?_, ?_, ?_, ?_, hD, h2D, hlarge,
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hSpos), hSX⟩
  · simpa using hpell
  · nlinarith
  · omega
  · omega

end DkMath.ABC
