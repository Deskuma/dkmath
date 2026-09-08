/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicThreeSectorIncidence
import DkMath.ABC.GNCubicPairedDepth
import DkMath.ABC.GNExcessCubicComplementPell

/-!
# Paired cubic orientations

This module freezes the exact arithmetic ledger for
`F(a) = GN 3 a 1` and `G(a) = GN 3 1 a`.  Ordinary common support is isolated
at `7`, while the non-exceptional repeated parts are coprime.  No relative
height, counting, density, or ABC closure statement is made.

The imported `exists_arbitrarily_large_coprime_cubic_repeated_parts` theorem
remains the absolute-size regression boundary.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## Paired values and the swap complement -/

def GNCubicForwardValue (a : ℕ) : ℕ := GN 3 a 1

def GNCubicSwapValue (a : ℕ) : ℕ := GN 3 1 a

noncomputable def GNCubicForwardRepeatedPart (a : ℕ) : ℕ :=
  GNNonExceptionalRepeatedPart 3 a 1

noncomputable def GNCubicSwapRepeatedPart (a : ℕ) : ℕ :=
  GNNonExceptionalRepeatedPart 3 1 a

theorem GNCubicForwardValue_eq_quadratic (a : ℕ) :
    GNCubicForwardValue a = a ^ 2 + 3 * a + 3 := by
  change GN 3 a 1 = _
  rw [GN_three_dual_explicit]
  ring

theorem GNCubicSwapValue_eq_quadratic (a : ℕ) :
    GNCubicSwapValue a = 3 * a ^ 2 + 3 * a + 1 := by
  change GN 3 1 a = _
  rw [GN_three_dual_explicit]
  ring

theorem three_not_dvd_GNCubicSwapValue (a : ℕ) :
    ¬ 3 ∣ GNCubicSwapValue a := by
  rw [GNCubicSwapValue_eq_quadratic]
  intro h
  have hz := Nat.mod_eq_zero_of_dvd h
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hz

theorem GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart
    (a : ℕ) :
    GNNonExceptionalRepeatedPart 3 1 a =
      repeatedPrimePowerPart (GN 3 1 a) := by
  have hn : GN 3 1 a ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  apply Nat.eq_of_factorization_eq
    (repeatedPrimePowerPart_pos _).ne'
    (repeatedPrimePowerPart_pos _).ne'
  intro q
  have hdepth : 2 ≤ (GN 3 1 a).factorization q →
      q ∈ GNNonExceptionalSupport 3 1 a := by
    intro hv
    have hs : q ∈ (GN 3 1 a).factorization.support :=
      Finsupp.mem_support_iff.mpr (by omega)
    have hp := (mem_support_factorization_iff.mp hs).2.1
    refine Finset.mem_filter.mpr ⟨hs, ?_⟩
    intro hq3
    have heq : q = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hq3).resolve_left hp.ne_one
    subst q
    have hd := (Nat.prime_three.pow_dvd_iff_le_factorization hn).mpr hv
    exact (three_not_dvd_GNCubicSwapValue a)
      (dvd_trans (dvd_pow_self 3 (by decide : (2 : ℕ) ≠ 0)) hd)
  rw [repeatedPrimePowerPart_factorization,
    repeatedPrimePowerPart_factorization]
  by_cases hs : q ∈ GNNonExceptionalSupport 3 1 a
  · rw [GNNonExceptionalPart_factorization_support,
      GNNonExceptionalPart_factorization, if_pos hs]
    have hq := (Finset.mem_filter.mp hs).1
    simp only [hs, hq, true_and]
  · have hv : ¬ 2 ≤ (GN 3 1 a).factorization q := fun h => hs (hdepth h)
    rw [GNNonExceptionalPart_factorization_support,
      GNNonExceptionalPart_factorization, if_neg hs]
    simp only [hs, hv, false_and, and_false, if_false]

noncomputable def GNExcessCubicSwapComplement (a : ℕ) : ℕ :=
  GN 3 1 a / GNNonExceptionalRepeatedPart 3 1 a

theorem GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement (a : ℕ) :
    GNNonExceptionalRepeatedPart 3 1 a * GNExcessCubicSwapComplement a =
      GN 3 1 a := by
  unfold GNExcessCubicSwapComplement
  exact Nat.mul_div_cancel' (GNNonExceptionalRepeatedPart_dvd_GN (by
    rw [GN_three_dual_explicit]
    positivity))

theorem GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement_eq_quadratic
    (a : ℕ) :
    GNNonExceptionalRepeatedPart 3 1 a * GNExcessCubicSwapComplement a =
      3 * a ^ 2 + 3 * a + 1 := by
  rw [GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement,
    GN_three_dual_explicit]
  ring

theorem squarefree_GNExcessCubicSwapComplement (a : ℕ) :
    Squarefree (GNExcessCubicSwapComplement a) := by
  rw [GNExcessCubicSwapComplement,
    GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart]
  exact squarefree_repeatedPrimePowerComplement (by
    rw [GN_three_dual_explicit]
    positivity)

theorem coprime_GNNonExceptionalRepeatedPart_GNExcessCubicSwapComplement
    (a : ℕ) :
    Nat.Coprime (GNNonExceptionalRepeatedPart 3 1 a)
      (GNExcessCubicSwapComplement a) := by
  rw [GNExcessCubicSwapComplement,
    GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart]
  exact coprime_repeatedPrimePowerPart_complement (by
    rw [GN_three_dual_explicit]
    positivity)

/-! ## Ordinary gcd and the exact mod-seven overlap -/

private theorem gcd_GN_three_one_swap_dvd_seven_aux (a : ℕ) :
    Nat.gcd (GN 3 a 1) (GN 3 1 a) ∣ 7 := by
  have h14 := gcd_GN_three_swap_dvd_fourteen a 1 (by simp)
  let d := Nat.gcd (GN 3 a 1) (GN 3 1 a)
  have hoddF : ¬ 2 ∣ GN 3 a 1 := by
    rw [GN_three_dual_explicit]
    intro h
    have hz := Nat.mod_eq_zero_of_dvd h
    have ha := Nat.mod_lt a (by decide : 0 < 2)
    interval_cases he : a % 2 <;>
      norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, he] at hz
  have hoddD : ¬ 2 ∣ d := by
    intro hd
    exact hoddF (dvd_trans hd (Nat.gcd_dvd_left _ _))
  have hcop : Nat.Coprime d 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).2 hoddD).symm
  have hd14 : d ∣ 2 * 7 := by simpa [d] using h14
  exact hcop.dvd_of_dvd_mul_left hd14

theorem gcd_GN_three_one_swap_dvd_seven (a : ℕ) :
    Nat.gcd (GN 3 a 1) (GN 3 1 a) ∣ 7 :=
  gcd_GN_three_one_swap_dvd_seven_aux a

theorem seven_dvd_both_cubic_orientations_iff_mod_eq_one (a : ℕ) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ↔ a % 7 = 1 := by
  constructor
  · rintro ⟨hF, hG⟩
    change 7 ∣ GNCubicForwardValue a at hF
    change 7 ∣ GNCubicSwapValue a at hG
    rw [GNCubicForwardValue_eq_quadratic] at hF
    rw [GNCubicSwapValue_eq_quadratic] at hG
    have hFz := Nat.mod_eq_zero_of_dvd hF
    have hGz := Nat.mod_eq_zero_of_dvd hG
    have ha := Nat.mod_lt a (by decide : 0 < 7)
    have haeq : a = 7 * (a / 7) + a % 7 := by omega
    rw [haeq] at hFz hGz
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hFz hGz
    interval_cases he : a % 7 <;> omega
  · intro ha
    change 7 ∣ GNCubicForwardValue a ∧ 7 ∣ GNCubicSwapValue a
    rw [GNCubicForwardValue_eq_quadratic, GNCubicSwapValue_eq_quadratic]
    have haeq : a = 7 * (a / 7) + 1 := by omega
    have hk : (7 * (a / 7) + 1) / 7 = a / 7 := by omega
    constructor
    · refine ⟨7 * (a / 7) ^ 2 + 5 * (a / 7) + 1, ?_⟩
      rw [haeq, hk]
      ring
    · refine ⟨21 * (a / 7) ^ 2 + 9 * (a / 7) + 1, ?_⟩
      rw [haeq, hk]
      ring

theorem gcd_GN_three_one_swap_eq_seven_iff_mod_eq_one (a : ℕ) :
    Nat.gcd (GN 3 a 1) (GN 3 1 a) = 7 ↔ a % 7 = 1 := by
  constructor
  · intro hg
    apply (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mp
    have h7g : 7 ∣ Nat.gcd (GN 3 a 1) (GN 3 1 a) := by
      rw [hg]
    exact ⟨h7g.trans (Nat.gcd_dvd_left _ _),
      h7g.trans (Nat.gcd_dvd_right _ _)⟩
  · intro ha
    have hboth := (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha
    have hdiv := gcd_GN_three_one_swap_dvd_seven a
    have h7g : 7 ∣ Nat.gcd (GN 3 a 1) (GN 3 1 a) := Nat.dvd_gcd hboth.1 hboth.2
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdiv with h1 | h7
    · exfalso
      have : ¬ (7 : ℕ) ∣ 1 := by norm_num
      rw [h1] at h7g
      exact this h7g
    · exact h7

theorem gcd_GN_three_one_swap_eq_one_iff_mod_ne_one (a : ℕ) :
    Nat.gcd (GN 3 a 1) (GN 3 1 a) = 1 ↔ a % 7 ≠ 1 := by
  constructor
  · intro hg ha
    have h7g : 7 ∣ Nat.gcd (GN 3 a 1) (GN 3 1 a) :=
      Nat.dvd_gcd ((seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha).1
        ((seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha).2
    rw [hg] at h7g
    norm_num at h7g
  · intro ha
    have hdiv := gcd_GN_three_one_swap_dvd_seven a
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdiv with h1 | h7
    · exact h1
    · exfalso
      apply ha
      exact (gcd_GN_three_one_swap_eq_seven_iff_mod_eq_one a).mp h7

theorem prime_dvd_both_cubic_orientations {a q : ℕ} (hq : Nat.Prime q)
    (hF : q ∣ GN 3 a 1) (hG : q ∣ GN 3 1 a) :
    q = 7 ∧ a % 7 = 1 := by
  have hqg : q ∣ Nat.gcd (GN 3 a 1) (GN 3 1 a) := Nat.dvd_gcd hF hG
  have hq7 : q ∣ 7 := hqg.trans (gcd_GN_three_one_swap_dvd_seven a)
  have hqeq : q = 7 :=
    (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hq7
  subst q
  exact ⟨rfl, (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mp
    ⟨hF, hG⟩⟩

/-! ## Repeated support and paired packets -/

theorem GNCubicPairedRepeatedParts_coprime {a : ℕ} (ha : 0 < a) :
    Nat.Coprime (GNCubicForwardRepeatedPart a)
      (GNCubicSwapRepeatedPart a) := by
  exact GNNonExceptionalRepeatedPart_three_coprime_swap ha (by norm_num) (by simp)

theorem GNCubicPairedRepeatedComplement_packet {a : ℕ} (ha : 0 < a) :
    GNCubicForwardRepeatedPart a * GNExcessCubicComplement a = GNCubicForwardValue a ∧
    GNCubicSwapRepeatedPart a * GNExcessCubicSwapComplement a = GNCubicSwapValue a ∧
    Squarefree (GNExcessCubicComplement a) ∧
    Squarefree (GNExcessCubicSwapComplement a) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a) (GNExcessCubicComplement a) ∧
    Nat.Coprime (GNCubicSwapRepeatedPart a) (GNExcessCubicSwapComplement a) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a) (GNCubicSwapRepeatedPart a) := by
  exact ⟨GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement a,
    GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement a,
    squarefree_GNExcessCubicComplement a,
    squarefree_GNExcessCubicSwapComplement a,
    coprime_GNNonExceptionalRepeatedPart_GNExcessCubicComplement a,
    coprime_GNNonExceptionalRepeatedPart_GNExcessCubicSwapComplement a,
    GNCubicPairedRepeatedParts_coprime ha⟩

theorem GNCubicPairedRepeatedComplement_product_identity {a : ℕ} (_ha : 0 < a) :
    (GNCubicForwardRepeatedPart a * GNExcessCubicComplement a) *
        (GNCubicSwapRepeatedPart a * GNExcessCubicSwapComplement a) =
      3 * (a + 1) ^ 4 + a ^ 2 := by
  change (GNNonExceptionalRepeatedPart 3 a 1 * GNExcessCubicComplement a) *
      (GNNonExceptionalRepeatedPart 3 1 a * GNExcessCubicSwapComplement a) = _
  rw [GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement,
    GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement]
  change GNCubicForwardValue a * GNCubicSwapValue a = _
  rw [GNCubicForwardValue_eq_quadratic, GNCubicSwapValue_eq_quadratic]
  exact cubicOrientation_product_identity_one a

theorem GNCubicPairedRepeatedProduct_dvd_quartic {a : ℕ} (ha : 0 < a) :
    GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a ∣
      3 * (a + 1) ^ 4 + a ^ 2 := by
  refine ⟨GNExcessCubicComplement a * GNExcessCubicSwapComplement a, ?_⟩
  calc
    3 * (a + 1) ^ 4 + a ^ 2 =
        (GNCubicForwardRepeatedPart a * GNExcessCubicComplement a) *
          (GNCubicSwapRepeatedPart a * GNExcessCubicSwapComplement a) :=
      (GNCubicPairedRepeatedComplement_product_identity ha).symm
    _ = (GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a) *
        (GNExcessCubicComplement a * GNExcessCubicSwapComplement a) := by
      ring

theorem GNCubicPairedRepeatedComplement_linear_difference {a : ℕ} (_ha : 0 < a) :
    (3 : ℤ) * ((GNCubicForwardRepeatedPart a * GNExcessCubicComplement a : ℕ) : ℤ) -
        ((GNCubicSwapRepeatedPart a * GNExcessCubicSwapComplement a : ℕ) : ℤ) =
      6 * (a : ℤ) + 8 := by
  change (3 : ℤ) *
      ((GNNonExceptionalRepeatedPart 3 a 1 * GNExcessCubicComplement a : ℕ) : ℤ) -
        ((GNNonExceptionalRepeatedPart 3 1 a * GNExcessCubicSwapComplement a : ℕ) : ℤ) = _
  rw [GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement,
    GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement]
  rw [GN_three_dual_explicit, GN_three_dual_explicit]
  push_cast
  ring

/-! ## Cross-gcd and the two mod-seven sectors -/

theorem gcd_dvd_seven_of_dvd_cubic_orientations {a A B : ℕ}
    (hA : A ∣ GN 3 a 1) (hB : B ∣ GN 3 1 a) :
    Nat.gcd A B ∣ 7 := by
  have hF : Nat.gcd A B ∣ GN 3 a 1 :=
    (Nat.gcd_dvd_left A B).trans hA
  have hG : Nat.gcd A B ∣ GN 3 1 a :=
    (Nat.gcd_dvd_right A B).trans hB
  exact (Nat.dvd_gcd hF hG).trans (gcd_GN_three_one_swap_dvd_seven a)

theorem GNCubicPaired_cross_gcd_packet {a : ℕ} (_ha : 0 < a) :
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) ∣ 7 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) ∣ 7 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) ∣ 7 := by
  have hMF : GNCubicForwardRepeatedPart a ∣ GN 3 a 1 := by
    refine ⟨GNExcessCubicComplement a, ?_⟩
    simpa [GNCubicForwardRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement a).symm
  have hSF : GNExcessCubicComplement a ∣ GN 3 a 1 := by
    refine ⟨GNCubicForwardRepeatedPart a, ?_⟩
    simpa [GNCubicForwardRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement a).symm
  have hMG : GNCubicSwapRepeatedPart a ∣ GN 3 1 a := by
    refine ⟨GNExcessCubicSwapComplement a, ?_⟩
    simpa [GNCubicSwapRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement a).symm
  have hSG : GNExcessCubicSwapComplement a ∣ GN 3 1 a := by
    refine ⟨GNCubicSwapRepeatedPart a, ?_⟩
    simpa [GNCubicSwapRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement a).symm
  exact ⟨gcd_dvd_seven_of_dvd_cubic_orientations hMF hSG,
    gcd_dvd_seven_of_dvd_cubic_orientations hSF hMG,
    gcd_dvd_seven_of_dvd_cubic_orientations hSF hSG⟩

theorem GNCubicPaired_offSeven_cross_coprime_packet {a : ℕ} (ha : 0 < a)
    (ha7 : a % 7 ≠ 1) :
    Nat.Coprime (GNCubicForwardRepeatedPart a) (GNCubicSwapRepeatedPart a) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a)
      (GNExcessCubicSwapComplement a) ∧
    Nat.Coprime (GNExcessCubicComplement a)
      (GNCubicSwapRepeatedPart a) ∧
    Nat.Coprime (GNExcessCubicComplement a)
      (GNExcessCubicSwapComplement a) := by
  have hMF : GNCubicForwardRepeatedPart a ∣ GN 3 a 1 := by
    refine ⟨GNExcessCubicComplement a, ?_⟩
    simpa [GNCubicForwardRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement a).symm
  have hSF : GNExcessCubicComplement a ∣ GN 3 a 1 := by
    refine ⟨GNCubicForwardRepeatedPart a, ?_⟩
    simpa [GNCubicForwardRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement a).symm
  have hMG : GNCubicSwapRepeatedPart a ∣ GN 3 1 a := by
    refine ⟨GNExcessCubicSwapComplement a, ?_⟩
    simpa [GNCubicSwapRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement a).symm
  have hSG : GNExcessCubicSwapComplement a ∣ GN 3 1 a := by
    refine ⟨GNCubicSwapRepeatedPart a, ?_⟩
    simpa [GNCubicSwapRepeatedPart, Nat.mul_comm] using
      (GNNonExceptionalRepeatedPart_mul_GNExcessCubicSwapComplement a).symm
  have hcross {A B : ℕ} (hdiv : Nat.gcd A B ∣ 7)
      (hA : A ∣ GN 3 a 1) (hB : B ∣ GN 3 1 a) : Nat.Coprime A B := by
    apply (Nat.coprime_iff_gcd_eq_one).2
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdiv with h1 | h7
    · exact h1
    · exfalso
      apply ha7
      apply (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mp
      have h7g : 7 ∣ Nat.gcd A B := by simp [h7]
      exact ⟨(h7g.trans (Nat.gcd_dvd_left _ _)).trans hA,
        (h7g.trans (Nat.gcd_dvd_right _ _)).trans hB⟩
  have hp := GNCubicPaired_cross_gcd_packet ha
  exact ⟨GNCubicPairedRepeatedParts_coprime ha, hcross hp.1 hMF hSG,
    hcross hp.2.1 hSF hMG, hcross hp.2.2 hSF hSG⟩

theorem GNCubicPaired_sevenSector_packet {a : ℕ} (ha : 0 < a)
    (ha7 : a % 7 = 1) :
    Nat.gcd (GN 3 a 1) (GN 3 1 a) = 7 ∧
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧
    ¬ (49 ∣ GN 3 a 1 ∧ 49 ∣ GN 3 1 a) ∧
    Nat.Coprime (GNCubicForwardRepeatedPart a) (GNCubicSwapRepeatedPart a) := by
  have hboth := (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha7
  have hsq := not_prime_sq_dvd_both_GN_three (a := a) (b := 1)
    (by simp) (by norm_num : Nat.Prime 7)
  have hsq' : ¬ (49 ∣ GN 3 a 1 ∧ 49 ∣ GN 3 1 a) := by
    simpa only [show (7 : ℕ) ^ 2 = 49 by norm_num] using hsq
  exact ⟨(gcd_GN_three_one_swap_eq_seven_iff_mod_eq_one a).mpr ha7,
    hboth.1, hboth.2, hsq', GNCubicPairedRepeatedParts_coprime ha⟩

end DkMath.ABC
