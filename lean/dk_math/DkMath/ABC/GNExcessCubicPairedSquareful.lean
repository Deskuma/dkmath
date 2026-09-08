/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicPairedOrientation
import DkMath.ABC.GNExcessCubicPellParameterIncidence

/-!
# Paired squareful and square-cube coordinates

This module consumes the paired orientation ledger and the canonical
squareful square-cube API.  It records exact factorization, support, and
coprimality facts only; no relative-height, counting, density, or ABC
closure statement is made.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## Generic and orientation squarefull facts -/

theorem repeatedPrimePowerPart_squarefull (n : ℕ) :
    squarefull (repeatedPrimePowerPart n) := by
  intro q hq hqdvd
  exact prime_sq_dvd_repeatedPrimePowerPart hq hqdvd

theorem GNCubicForwardRepeatedPart_squarefull (a : ℕ) :
    squarefull (GNCubicForwardRepeatedPart a) := by
  change squarefull (GNNonExceptionalRepeatedPart 3 a 1)
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart]
  exact repeatedPrimePowerPart_squarefull _

theorem GNCubicSwapRepeatedPart_squarefull (a : ℕ) :
    squarefull (GNCubicSwapRepeatedPart a) := by
  change squarefull (GNNonExceptionalRepeatedPart 3 1 a)
  rw [GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart]
  exact repeatedPrimePowerPart_squarefull _

theorem GNCubicForwardRepeatedPart_pos (a : ℕ) :
    0 < GNCubicForwardRepeatedPart a := by
  change 0 < GNNonExceptionalRepeatedPart 3 a 1
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart]
  exact repeatedPrimePowerPart_pos _

theorem GNCubicSwapRepeatedPart_pos (a : ℕ) :
    0 < GNCubicSwapRepeatedPart a := by
  change 0 < GNNonExceptionalRepeatedPart 3 1 a
  rw [GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart]
  exact repeatedPrimePowerPart_pos _

/-! ## Canonical square-cube coordinates -/

theorem GNCubicPairedRepeatedParts_squareCube_packet {a : ℕ} (_ha : 0 < a) :
    GNCubicForwardRepeatedPart a =
        (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a)) ^ 2 *
          (oddPart (GNCubicForwardRepeatedPart a)) ^ 3 ∧
    GNCubicSwapRepeatedPart a =
        (GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) ^ 2 *
          (oddPart (GNCubicSwapRepeatedPart a)) ^ 3 ∧
    Squarefree (oddPart (GNCubicForwardRepeatedPart a)) ∧
    Squarefree (oddPart (GNCubicSwapRepeatedPart a)) ∧
    0 < oddPart (GNCubicForwardRepeatedPart a) ∧
    0 < oddPart (GNCubicSwapRepeatedPart a) ∧
    0 < GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a) ∧
    0 < GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a) := by
  have hFp := GNCubicForwardRepeatedPart_pos a
  have hGp := GNCubicSwapRepeatedPart_pos a
  have hFf := GNCubicForwardRepeatedPart_squarefull a
  have hGf := GNCubicSwapRepeatedPart_squarefull a
  have hFc := squareful_eq_squareQuotient_sq_mul_oddPart_cube
    (Nat.ne_of_gt hFp) hFf
  have hGc := squareful_eq_squareQuotient_sq_mul_oddPart_cube
    (Nat.ne_of_gt hGp) hGf
  have hFr : 0 < oddPart (GNCubicForwardRepeatedPart a) := by
    have hsf := squarefree_oddPart (GNCubicForwardRepeatedPart a)
    have hdiv := oddPart_dvd_of_squarefull (Nat.ne_of_gt hFp) hFf
    exact Nat.pos_of_ne_zero (by
      intro hr
      rw [hr] at hFc
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hFc
      exact (Nat.ne_of_gt hFp) hFc)
  have hGr : 0 < oddPart (GNCubicSwapRepeatedPart a) := by
    have hdiv := oddPart_dvd_of_squarefull (Nat.ne_of_gt hGp) hGf
    exact Nat.pos_of_ne_zero (by
      intro hr
      rw [hr] at hGc
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hGc
      exact (Nat.ne_of_gt hGp) hGc)
  have hFu : 0 < GNExcessCubicSquarefulQuotient
      (GNCubicForwardRepeatedPart a) := by
    by_contra hu
    have hu0 := Nat.eq_zero_of_not_pos hu
    rw [hu0] at hFc
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hFc
    exact (Nat.ne_of_gt hFp) hFc
  have hGu : 0 < GNExcessCubicSquarefulQuotient
      (GNCubicSwapRepeatedPart a) := by
    by_contra hu
    have hu0 := Nat.eq_zero_of_not_pos hu
    rw [hu0] at hGc
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hGc
    exact (Nat.ne_of_gt hGp) hGc
  exact ⟨hFc, hGc, squarefree_oddPart _, squarefree_oddPart _,
    hFr, hGr, hFu, hGu⟩

theorem GNCubicPairedRepeatedProduct_squarefull {a : ℕ} (_ha : 0 < a) :
    squarefull (GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a) := by
  intro q hq hqdvd
  rcases hq.dvd_mul.mp hqdvd with hF | hG
  · exact dvd_mul_of_dvd_left (GNCubicForwardRepeatedPart_squarefull a q hq hF) _
  · exact dvd_mul_of_dvd_right (GNCubicSwapRepeatedPart_squarefull a q hq hG) _

theorem GNCubicPairedRepeatedProduct_squareCube_identity {a : ℕ} (ha : 0 < a) :
    GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a =
      (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a) *
        GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) ^ 2 *
      (oddPart (GNCubicForwardRepeatedPart a) *
        oddPart (GNCubicSwapRepeatedPart a)) ^ 3 := by
  obtain ⟨hFc, hGc, _, _, _, _, _, _⟩ :=
    GNCubicPairedRepeatedParts_squareCube_packet ha
  calc
    GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a =
        (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a)) ^ 2 *
          (oddPart (GNCubicForwardRepeatedPart a)) ^ 3 *
        ((GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) ^ 2 *
          (oddPart (GNCubicSwapRepeatedPart a)) ^ 3) :=
      congrArg₂ (· * ·) hFc hGc
    _ = _ := by ring

theorem GNCubicPaired_squareCube_cross_coprime_packet {a : ℕ} (ha : 0 < a) :
    Nat.Coprime (oddPart (GNCubicForwardRepeatedPart a))
      (oddPart (GNCubicSwapRepeatedPart a)) ∧
    Nat.Coprime (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a))
      (GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) := by
  have hMF := GNCubicForwardRepeatedPart_pos a
  have hMG := GNCubicSwapRepeatedPart_pos a
  have hFF := GNCubicForwardRepeatedPart_squarefull a
  have hGF := GNCubicSwapRepeatedPart_squarefull a
  have hcop := GNCubicPairedRepeatedParts_coprime ha
  have hrF := oddPart_dvd_of_squarefull (Nat.ne_of_gt hMF) hFF
  have hrG := oddPart_dvd_of_squarefull (Nat.ne_of_gt hMG) hGF
  have huF := GNExcessCubicSquarefulQuotient_dvd_of_squarefull
    (Nat.ne_of_gt hMF) hFF
  have huG := GNExcessCubicSquarefulQuotient_dvd_of_squarefull
    (Nat.ne_of_gt hMG) hGF
  exact ⟨Nat.Coprime.of_dvd hrF hrG hcop,
    Nat.Coprime.of_dvd huF huG hcop⟩

theorem GNCubicPairedRepeatedProduct_oddPartProduct_squarefree {a : ℕ}
    (ha : 0 < a) :
    Squarefree (oddPart (GNCubicForwardRepeatedPart a) *
      oddPart (GNCubicSwapRepeatedPart a)) := by
  have hp := GNCubicPairedRepeatedParts_squareCube_packet ha
  have hc := GNCubicPaired_squareCube_cross_coprime_packet ha
  exact squarefree_mul_iff.mpr
    ⟨Nat.coprime_iff_isRelPrime.mp hc.1, hp.2.2.1, hp.2.2.2.1⟩

/-! ## Prime support and quartic consumers -/

theorem GNCubicForwardRepeatedPart_prime_mod_three_eq_one
    {a q : ℕ} (hq : Nat.Prime q)
    (hqdvd : q ∣ GNCubicForwardRepeatedPart a) :
    q % 3 = 1 := by
  by_cases ha : 0 < a
  · change q ∣ GNNonExceptionalRepeatedPart 3 a 1 at hqdvd
    have hqS := prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart hq hqdvd
    let T : Triple := Triple.mk a 1 (a + 1) rfl (by simp)
    exact T.mod_eq_one_of_mem_GNNonExceptionalSupport Nat.prime_three ha hqS
  · have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    change q ∣ GNNonExceptionalRepeatedPart 3 0 1 at hqdvd
    rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart] at hqdvd
    have hGN : GN 3 0 1 = 3 := by
      rw [GN_three_dual_explicit]
      norm_num
    rw [hGN] at hqdvd
    have hq2 := prime_sq_dvd_repeatedPrimePowerPart hq hqdvd
    have hq2le : q ^ 2 ≤ 3 := Nat.le_of_dvd (by norm_num)
      (hq2.trans (repeatedPrimePowerPart_dvd (by norm_num)))
    exfalso
    nlinarith [hq.two_le]

theorem GNCubicSwapRepeatedPart_prime_mod_three_eq_one
    {a q : ℕ} (hq : Nat.Prime q)
    (hqdvd : q ∣ GNCubicSwapRepeatedPart a) :
    q % 3 = 1 := by
  change q ∣ GNNonExceptionalRepeatedPart 3 1 a at hqdvd
  have hqS := prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart hq hqdvd
  let T : Triple := Triple.mk 1 a (1 + a) rfl (by simp)
  exact T.mod_eq_one_of_mem_GNNonExceptionalSupport Nat.prime_three (by norm_num) hqS

theorem GNCubicPairedRepeatedProduct_prime_mod_three_eq_one
    {a q : ℕ} (hq : Nat.Prime q)
    (hqdvd : q ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a) :
    q % 3 = 1 := by
  rcases hq.dvd_mul.mp hqdvd with hF | hG
  · exact GNCubicForwardRepeatedPart_prime_mod_three_eq_one hq hF
  · exact GNCubicSwapRepeatedPart_prime_mod_three_eq_one hq hG

theorem GNCubicPairedRepeatedProduct_squareful_packet {a : ℕ} (ha : 0 < a) :
    squarefull (GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a) ∧
    GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a =
      (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a) *
        GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) ^ 2 *
      (oddPart (GNCubicForwardRepeatedPart a) *
        oddPart (GNCubicSwapRepeatedPart a)) ^ 3 ∧
    Squarefree (oddPart (GNCubicForwardRepeatedPart a) *
      oddPart (GNCubicSwapRepeatedPart a)) ∧
    GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a ∣
      3 * (a + 1) ^ 4 + a ^ 2 := by
  exact ⟨GNCubicPairedRepeatedProduct_squarefull ha,
    GNCubicPairedRepeatedProduct_squareCube_identity ha,
    GNCubicPairedRepeatedProduct_oddPartProduct_squarefree ha,
    GNCubicPairedRepeatedProduct_dvd_quartic ha⟩

theorem GNCubicPairedRepeatedProduct_prime_sq_dvd
    {a q : ℕ} (ha : 0 < a) (hq : Nat.Prime q)
    (hqdvd : q ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a) :
    q ^ 2 ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a := by
  exact GNCubicPairedRepeatedProduct_squarefull ha q hq hqdvd

theorem GNCubicPairedRepeatedProduct_prime_sq_dvd_quartic
    {a q : ℕ} (ha : 0 < a) (hq : Nat.Prime q)
    (hqdvd : q ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a) :
    q ^ 2 ∣ 3 * (a + 1) ^ 4 + a ^ 2 := by
  exact (GNCubicPairedRepeatedProduct_prime_sq_dvd ha hq hqdvd).trans
    (GNCubicPairedRepeatedProduct_dvd_quartic ha)

/-! ## Sector consumers -/

theorem GNCubicPaired_offSeven_squareCube_packet {a : ℕ} (ha : 0 < a)
    (ha7 : a % 7 ≠ 1) :
    GNCubicForwardRepeatedPart a =
        (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a)) ^ 2 *
          (oddPart (GNCubicForwardRepeatedPart a)) ^ 3 ∧
    GNCubicSwapRepeatedPart a =
        (GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) ^ 2 *
          (oddPart (GNCubicSwapRepeatedPart a)) ^ 3 ∧
    Squarefree (oddPart (GNCubicForwardRepeatedPart a)) ∧
    Squarefree (oddPart (GNCubicSwapRepeatedPart a)) ∧
    Nat.Coprime (oddPart (GNCubicForwardRepeatedPart a))
      (oddPart (GNCubicSwapRepeatedPart a)) ∧
    Nat.Coprime (GNExcessCubicSquarefulQuotient (GNCubicForwardRepeatedPart a))
      (GNExcessCubicSquarefulQuotient (GNCubicSwapRepeatedPart a)) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a) (GNCubicSwapRepeatedPart a) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a)
      (GNExcessCubicSwapComplement a) ∧
    Nat.Coprime (GNExcessCubicComplement a)
      (GNCubicSwapRepeatedPart a) ∧
    Nat.Coprime (GNExcessCubicComplement a)
      (GNExcessCubicSwapComplement a) := by
  have hp := GNCubicPairedRepeatedParts_squareCube_packet ha
  have hc := GNCubicPaired_squareCube_cross_coprime_packet ha
  have ho := GNCubicPaired_offSeven_cross_coprime_packet ha ha7
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hc.1, hc.2,
    ho.1, ho.2.1, ho.2.2.1, ho.2.2.2⟩

theorem GNCubicPaired_sevenSector_squareful_packet {a : ℕ} (ha : 0 < a)
    (ha7 : a % 7 = 1) :
    Nat.gcd (GN 3 a 1) (GN 3 1 a) = 7 ∧
    ¬ (49 ∣ GN 3 a 1 ∧ 49 ∣ GN 3 1 a) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a) (GNCubicSwapRepeatedPart a) ∧
    squarefull (GNCubicForwardRepeatedPart a) ∧
    squarefull (GNCubicSwapRepeatedPart a) := by
  have hs := GNCubicPaired_sevenSector_packet ha ha7
  exact ⟨hs.1, hs.2.2.2.1, hs.2.2.2.2,
    GNCubicForwardRepeatedPart_squarefull a,
    GNCubicSwapRepeatedPart_squarefull a⟩

end DkMath.ABC
