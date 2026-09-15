/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicPairedSquareful

#print "file: DkMath.ABC.GNExcessCubicSevenDepth"

/-!
# LUNA-020: seven-depth state normalization

This module freezes the exact mod-49 states of the paired cubic orientations.
It records local divisibility and gcd data only; no counting, density,
relative-height, or ABC closure statement is made.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## Repeated-prime membership and orientation depth -/

theorem prime_dvd_repeatedPrimePowerPart_iff_sq_dvd
    {n q : ℕ} (hq : Nat.Prime q) (hn : n ≠ 0) :
    q ∣ repeatedPrimePowerPart n ↔ q ^ 2 ∣ n := by
  constructor
  · intro hqrep
    exact (prime_sq_dvd_repeatedPrimePowerPart hq hqrep).trans
      (repeatedPrimePowerPart_dvd hn)
  · intro hq2
    have hv : 2 ≤ n.factorization q :=
      (hq.pow_dvd_iff_le_factorization hn).mp hq2
    have hmem : q ∈ n.factorization.support :=
      mem_support_factorization_iff.mpr ⟨hn, hq,
        (dvd_pow_self q (by omega : (2 : ℕ) ≠ 0)).trans hq2⟩
    unfold repeatedPrimePowerPart
    exact (dvd_pow_self q (by omega : n.factorization q ≠ 0)).trans
      (Finset.dvd_prod_of_mem (a := q) (s := n.factorization.support.filter
        (fun p => 2 ≤ n.factorization p)) (fun p => p ^ n.factorization p)
        (Finset.mem_filter.mpr ⟨hmem, hv⟩))

theorem seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value (a : ℕ) :
    7 ∣ GNCubicForwardRepeatedPart a ↔ 49 ∣ GN 3 a 1 := by
  change 7 ∣ GNNonExceptionalRepeatedPart 3 a 1 ↔ 49 ∣ GN 3 a 1
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart]
  have hn : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  simpa only [show (7 : ℕ) ^ 2 = 49 by norm_num] using
    (prime_dvd_repeatedPrimePowerPart_iff_sq_dvd
      (n := GN 3 a 1) (q := 7) (by norm_num) hn)

theorem seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value (a : ℕ) :
    7 ∣ GNCubicSwapRepeatedPart a ↔ 49 ∣ GN 3 1 a := by
  change 7 ∣ GNNonExceptionalRepeatedPart 3 1 a ↔ 49 ∣ GN 3 1 a
  rw [GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart]
  have hn : GN 3 1 a ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  simpa only [show (7 : ℕ) ^ 2 = 49 by norm_num] using
    (prime_dvd_repeatedPrimePowerPart_iff_sq_dvd
      (n := GN 3 1 a) (q := 7) (by norm_num) hn)

/-! ## Algebraic seven-sector lift -/

theorem GNCubicForwardValue_eq_seven_mul_of_mod_seven_eq_one
    {a : ℕ} (ha7 : a % 7 = 1) :
    GNCubicForwardValue a =
      7 * (7 * (a / 7) ^ 2 + 5 * (a / 7) + 1) := by
  have ha : a = 7 * (a / 7) + 1 := by omega
  have hk : (7 * (a / 7) + 1) / 7 = a / 7 := by omega
  rw [GNCubicForwardValue_eq_quadratic, ha, hk]
  ring

theorem GNCubicSwapValue_eq_seven_mul_of_mod_seven_eq_one
    {a : ℕ} (ha7 : a % 7 = 1) :
    GNCubicSwapValue a =
      7 * (21 * (a / 7) ^ 2 + 9 * (a / 7) + 1) := by
  have ha : a = 7 * (a / 7) + 1 := by omega
  have hk : (7 * (a / 7) + 1) / 7 = a / 7 := by omega
  rw [GNCubicSwapValue_eq_quadratic, ha, hk]
  ring

private theorem seven_dvd_five_mul_add_one_iff_mod_eq_four (k : ℕ) :
    7 ∣ 5 * k + 1 ↔ k % 7 = 4 := by
  constructor
  · intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hk := Nat.mod_lt k (by decide : 0 < 7)
    have hz' : (5 * (k % 7) + 1) % 7 = 0 := by
      simpa [Nat.add_mod, Nat.mul_mod] using hz
    omega
  · intro hk
    have hkeq : k = 7 * (k / 7) + 4 := by omega
    rw [hkeq]
    refine ⟨5 * (k / 7) + 3, ?_⟩
    ring

private theorem seven_dvd_two_mul_add_one_iff_mod_eq_three (k : ℕ) :
    7 ∣ 2 * k + 1 ↔ k % 7 = 3 := by
  constructor
  · intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hk := Nat.mod_lt k (by decide : 0 < 7)
    have hz' : (2 * (k % 7) + 1) % 7 = 0 := by
      simpa [Nat.add_mod, Nat.mul_mod] using hz
    omega
  · intro hk
    have hkeq : k = 7 * (k / 7) + 3 := by omega
    rw [hkeq]
    refine ⟨2 * (k / 7) + 1, ?_⟩
    ring

theorem fortyNine_dvd_GNCubicForwardValue_iff_mod_eq_twentyNine
    {a : ℕ} (ha7 : a % 7 = 1) :
    49 ∣ GNCubicForwardValue a ↔ a % 49 = 29 := by
  let k := a / 7
  have hfac := GNCubicForwardValue_eq_seven_mul_of_mod_seven_eq_one ha7
  have hmod : 7 ∣ 5 * k + 1 ↔ k % 7 = 4 :=
    seven_dvd_five_mul_add_one_iff_mod_eq_four k
  have hlift : a = 7 * k + 1 := by
    dsimp [k]
    omega
  have hres : k % 7 = 4 ↔ a % 49 = 29 := by
    constructor
    · intro hk
      have hkeq : k = 7 * (k / 7) + 4 := by omega
      rw [hlift, hkeq]
      have hq : (7 * (7 * (k / 7) + 4) + 1) % 49 = 29 := by
        have heq : 7 * (7 * (k / 7) + 4) + 1 = 49 * (k / 7) + 29 := by ring
        rw [heq]
        simp
      exact hq
    · intro ha49
      have hk49 := Nat.mod_lt a (by decide : 0 < 49)
      have hk7 := Nat.mod_lt k (by decide : 0 < 7)
      have hkeq : a = 7 * k + 1 := hlift
      rw [hkeq] at ha49
      have heq : k = 7 * (k / 7) + (k % 7) := by omega
      rw [heq] at ha49
      omega
  constructor
  · intro h49
    have h7 : 7 ∣ 7 * k ^ 2 + 5 * k + 1 := by
      apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7)
      simpa [hfac, k, show (49 : ℕ) = 7 * 7 by norm_num] using h49
    have h5 : 7 ∣ 5 * k + 1 := by
      have hrest : 7 ∣ 7 * k ^ 2 := ⟨k ^ 2, by ring⟩
      have h7' : 7 ∣ 7 * k ^ 2 + (5 * k + 1) := by simpa [add_assoc] using h7
      exact (Nat.dvd_add_iff_right (k := 7) (m := 7 * k ^ 2)
        (n := 5 * k + 1) hrest).mpr h7'
    exact hres.mp (hmod.mp h5)
  · intro ha49
    have hk4 := hres.mpr ha49
    have h5 := hmod.mpr hk4
    have h7 : 7 ∣ 7 * k ^ 2 + 5 * k + 1 := by
      have hrest : 7 ∣ 7 * k ^ 2 := ⟨k ^ 2, by ring⟩
      have h7' : 7 ∣ 7 * k ^ 2 + (5 * k + 1) :=
        (Nat.dvd_add_iff_right (k := 7) (m := 7 * k ^ 2)
          (n := 5 * k + 1) hrest).mp h5
      simpa [add_assoc] using h7'
    rw [hfac]
    exact (Nat.mul_dvd_mul_left 7 h7)

theorem fortyNine_dvd_GNCubicSwapValue_iff_mod_eq_twentyTwo
    {a : ℕ} (ha7 : a % 7 = 1) :
    49 ∣ GNCubicSwapValue a ↔ a % 49 = 22 := by
  let k := a / 7
  have hfac := GNCubicSwapValue_eq_seven_mul_of_mod_seven_eq_one ha7
  have hmod : 7 ∣ 2 * k + 1 ↔ k % 7 = 3 :=
    seven_dvd_two_mul_add_one_iff_mod_eq_three k
  have hlift : a = 7 * k + 1 := by
    dsimp [k]
    omega
  have hres : k % 7 = 3 ↔ a % 49 = 22 := by
    constructor
    · intro hk
      have hkeq : k = 7 * (k / 7) + 3 := by omega
      rw [hlift, hkeq]
      have heq : 7 * (7 * (k / 7) + 3) + 1 = 49 * (k / 7) + 22 := by ring
      rw [heq]
      simp
    · intro ha49
      have hk49 := Nat.mod_lt a (by decide : 0 < 49)
      have hk7 := Nat.mod_lt k (by decide : 0 < 7)
      rw [hlift] at ha49
      have heq : k = 7 * (k / 7) + (k % 7) := by omega
      rw [heq] at ha49
      omega
  constructor
  · intro h49
    have h7 : 7 ∣ 21 * k ^ 2 + 9 * k + 1 := by
      apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7)
      simpa [hfac, k, show (49 : ℕ) = 7 * 7 by norm_num] using h49
    have h2 : 7 ∣ 2 * k + 1 := by
      have hrest : 7 ∣ 21 * k ^ 2 + 7 * k :=
        ⟨3 * k ^ 2 + k, by ring⟩
      have hrewrite : 21 * k ^ 2 + 9 * k + 1 =
          (21 * k ^ 2 + 7 * k) + (2 * k + 1) := by ring
      have h7' : 7 ∣ (21 * k ^ 2 + 7 * k) + (2 * k + 1) := by
        simpa [hrewrite] using h7
      exact (Nat.dvd_add_iff_right
        (k := 7) (m := 21 * k ^ 2 + 7 * k) (n := 2 * k + 1) hrest).mpr h7'
    exact hres.mp (hmod.mp h2)
  · intro ha49
    have hk3 := hres.mpr ha49
    have h2 := hmod.mpr hk3
    have h7 : 7 ∣ 21 * k ^ 2 + 9 * k + 1 := by
      have hrest : 7 ∣ 21 * k ^ 2 + 7 * k :=
        ⟨3 * k ^ 2 + k, by ring⟩
      have hrewrite : 21 * k ^ 2 + 9 * k + 1 =
          (21 * k ^ 2 + 7 * k) + (2 * k + 1) := by ring
      have h7' : 7 ∣ (21 * k ^ 2 + 7 * k) + (2 * k + 1) :=
        (Nat.dvd_add_iff_right (k := 7) (m := 21 * k ^ 2 + 7 * k)
          (n := 2 * k + 1) hrest).mp h2
      simpa [hrewrite] using h7'
    rw [hfac]
    exact Nat.mul_dvd_mul_left 7 h7

/-! ## Exact seven-depth packets -/

theorem not_fortyNine_dvd_both_cubic_orientations (a : ℕ) :
    ¬ (49 ∣ GN 3 a 1 ∧ 49 ∣ GN 3 1 a) := by
  have h := not_prime_sq_dvd_both_GN_three (a := a) (b := 1)
    (by simp : Nat.Coprime a 1) (by norm_num : Nat.Prime 7)
  simpa only [show (7 : ℕ) ^ 2 = 49 by norm_num] using h

theorem not_sevenDepth_residues (a : ℕ) :
    ¬ (a % 49 = 29 ∧ a % 49 = 22) := by omega

private theorem seven_dvd_right_of_dvd_mul_of_not_left {x y : ℕ}
    (hxy : 7 ∣ x * y) (hx : ¬ 7 ∣ x) : 7 ∣ y := by
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hxy with h | h
  · exact (hx h).elim
  · exact h

private theorem not_seven_of_coprime_dvd_left {x y : ℕ}
    (hcop : Nat.Coprime x y) (hx : 7 ∣ x) : ¬ 7 ∣ y := by
  intro hy
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 7) hx hy) hcop

private theorem gcd_eq_seven_of_dvd_seven {x y : ℕ}
    (hdiv : Nat.gcd x y ∣ 7) (hx : 7 ∣ x) (hy : 7 ∣ y) :
    Nat.gcd x y = 7 := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdiv with h1 | h7
  · have hbad : 7 ∣ 1 := by simpa [h1] using (Nat.dvd_gcd hx hy)
    norm_num at hbad
  · exact h7

private theorem gcd_eq_one_of_dvd_seven_of_not_both {x y : ℕ}
    (hdiv : Nat.gcd x y ∣ 7) (hx : ¬ 7 ∣ x) (_hy : ¬ 7 ∣ y) :
    Nat.gcd x y = 1 := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdiv with h1 | h7
  · exact h1
  · exfalso
    apply hx
    have h7g : 7 ∣ Nat.gcd x y := by simp [h7]
    exact h7g.trans (Nat.gcd_dvd_left _ _)

private theorem gcd_eq_one_of_dvd_seven_of_not_left {x y : ℕ}
    (hdiv : Nat.gcd x y ∣ 7) (hx : ¬ 7 ∣ x) : Nat.gcd x y = 1 := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdiv with h1 | h7
  · exact h1
  · exfalso
    apply hx
    have h7g : 7 ∣ Nat.gcd x y := by simp [h7]
    exact h7g.trans (Nat.gcd_dvd_left _ _)

private theorem gcd_eq_one_of_dvd_seven_of_not_right {x y : ℕ}
    (hdiv : Nat.gcd x y ∣ 7) (hy : ¬ 7 ∣ y) : Nat.gcd x y = 1 := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdiv with h1 | h7
  · exact h1
  · exfalso
    apply hy
    have h7g : 7 ∣ Nat.gcd x y := by simp [h7]
    exact h7g.trans (Nat.gcd_dvd_right _ _)

theorem GNCubicPaired_forwardSevenDeep_packet {a : ℕ}
    (ha : 0 < a) (ha49 : a % 49 = 29) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧ 49 ∣ GN 3 a 1 ∧
    ¬ 49 ∣ GN 3 1 a ∧ 7 ∣ GNCubicForwardRepeatedPart a ∧
    ¬ 7 ∣ GNCubicSwapRepeatedPart a ∧
    ¬ 7 ∣ GNExcessCubicComplement a ∧
    7 ∣ GNExcessCubicSwapComplement a := by
  have ha7 : a % 7 = 1 := by omega
  have hFG7 := (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha7
  have hF49' := (fortyNine_dvd_GNCubicForwardValue_iff_mod_eq_twentyNine (a := a) ha7).mpr ha49
  have hF49 : 49 ∣ GN 3 a 1 := by
    simpa [GNCubicForwardValue] using hF49'
  have hG49 : ¬ 49 ∣ GN 3 1 a := by
    intro h
    exact not_fortyNine_dvd_both_cubic_orientations a ⟨hF49, h⟩
  have hMF7 := (seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value a).mpr hF49
  have hMG7 : ¬ 7 ∣ GNCubicSwapRepeatedPart a := by
    intro h
    exact hG49 ((seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value a).mp h)
  obtain ⟨hMFs, hMGs, _, _, hcFS, hcGS, _⟩ :=
    GNCubicPairedRepeatedComplement_packet ha
  have hSF7 : ¬ 7 ∣ GNExcessCubicComplement a :=
    not_seven_of_coprime_dvd_left hcFS hMF7
  have hSG7 : 7 ∣ GNExcessCubicSwapComplement a := by
    apply seven_dvd_right_of_dvd_mul_of_not_left (x := GNCubicSwapRepeatedPart a)
      (y := GNExcessCubicSwapComplement a) (hx := hMG7)
    simpa [hMGs, GNCubicSwapValue] using hFG7.2
  exact ⟨hFG7.1, hFG7.2, hF49, hG49, hMF7, hMG7, hSF7, hSG7⟩

theorem GNCubicPaired_swapSevenDeep_packet {a : ℕ}
    (ha : 0 < a) (ha49 : a % 49 = 22) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧ ¬ 49 ∣ GN 3 a 1 ∧
    49 ∣ GN 3 1 a ∧ ¬ 7 ∣ GNCubicForwardRepeatedPart a ∧
    7 ∣ GNCubicSwapRepeatedPart a ∧
    7 ∣ GNExcessCubicComplement a ∧
    ¬ 7 ∣ GNExcessCubicSwapComplement a := by
  have ha7 : a % 7 = 1 := by omega
  have hFG7 := (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha7
  have hG49' := (fortyNine_dvd_GNCubicSwapValue_iff_mod_eq_twentyTwo (a := a) ha7).mpr ha49
  have hG49 : 49 ∣ GN 3 1 a := by
    simpa [GNCubicSwapValue] using hG49'
  have hF49 : ¬ 49 ∣ GN 3 a 1 := by
    intro h
    exact not_fortyNine_dvd_both_cubic_orientations a ⟨h, hG49⟩
  have hMF7 : ¬ 7 ∣ GNCubicForwardRepeatedPart a := by
    intro h
    exact hF49 ((seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value a).mp h)
  have hMG7 := (seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value a).mpr hG49
  obtain ⟨hMFs, hMGs, _, _, hcFS, hcGS, _⟩ :=
    GNCubicPairedRepeatedComplement_packet ha
  have hSF7 : 7 ∣ GNExcessCubicComplement a := by
    apply seven_dvd_right_of_dvd_mul_of_not_left (x := GNCubicForwardRepeatedPart a)
      (y := GNExcessCubicComplement a) (hx := hMF7)
    simpa [hMFs, GNCubicForwardValue] using hFG7.1
  have hSG7 : ¬ 7 ∣ GNExcessCubicSwapComplement a :=
    not_seven_of_coprime_dvd_left hcGS hMG7
  exact ⟨hFG7.1, hFG7.2, hF49, hG49, hMF7, hMG7, hSF7, hSG7⟩

theorem GNCubicPaired_shallowSeven_packet {a : ℕ}
    (ha : 0 < a) (ha7 : a % 7 = 1)
    (h29 : a % 49 ≠ 29) (h22 : a % 49 ≠ 22) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧
    ¬ 49 ∣ GN 3 a 1 ∧ ¬ 49 ∣ GN 3 1 a ∧
    ¬ 7 ∣ GNCubicForwardRepeatedPart a ∧
    ¬ 7 ∣ GNCubicSwapRepeatedPart a ∧
    7 ∣ GNExcessCubicComplement a ∧
    7 ∣ GNExcessCubicSwapComplement a := by
  have hFG7 := (seven_dvd_both_cubic_orientations_iff_mod_eq_one a).mpr ha7
  have hF49 : ¬ 49 ∣ GN 3 a 1 := by
    intro h
    exact h29 ((fortyNine_dvd_GNCubicForwardValue_iff_mod_eq_twentyNine ha7).mp h)
  have hG49 : ¬ 49 ∣ GN 3 1 a := by
    intro h
    exact h22 ((fortyNine_dvd_GNCubicSwapValue_iff_mod_eq_twentyTwo ha7).mp h)
  have hMF7 : ¬ 7 ∣ GNCubicForwardRepeatedPart a := by
    intro h
    exact hF49 ((seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value a).mp h)
  have hMG7 : ¬ 7 ∣ GNCubicSwapRepeatedPart a := by
    intro h
    exact hG49 ((seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value a).mp h)
  obtain ⟨hMFs, hMGs, _, _, hcFS, hcGS, _⟩ :=
    GNCubicPairedRepeatedComplement_packet ha
  have hSF7 : 7 ∣ GNExcessCubicComplement a := by
    apply seven_dvd_right_of_dvd_mul_of_not_left (x := GNCubicForwardRepeatedPart a)
      (y := GNExcessCubicComplement a) (hx := hMF7)
    simpa [hMFs, GNCubicForwardValue] using hFG7.1
  have hSG7 : 7 ∣ GNExcessCubicSwapComplement a := by
    apply seven_dvd_right_of_dvd_mul_of_not_left (x := GNCubicSwapRepeatedPart a)
      (y := GNExcessCubicSwapComplement a) (hx := hMG7)
    simpa [hMGs, GNCubicSwapValue] using hFG7.2
  exact ⟨hFG7.1, hFG7.2, hF49, hG49, hMF7, hMG7, hSF7, hSG7⟩

theorem GNCubicPaired_forwardSevenDeep_crossGcd_packet {a : ℕ}
    (ha : 0 < a) (ha49 : a % 49 = 29) :
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) = 7 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNCubicSwapRepeatedPart a) = 1 := by
  have hs := GNCubicPaired_forwardSevenDeep_packet ha ha49
  rcases hs with ⟨hF7, hG7, hF49, hG49, hMF, hMG, hSF, hSG⟩
  have hc := GNCubicPaired_cross_gcd_packet ha
  obtain ⟨hMFs, hMGs, _, _, hcFS, hcGS, hcFG⟩ :=
    GNCubicPairedRepeatedComplement_packet ha
  have hrep := GNCubicPairedRepeatedParts_coprime ha
  exact ⟨gcd_eq_seven_of_dvd_seven hc.1 hMF hSG,
    gcd_eq_one_of_dvd_seven_of_not_both hc.2.1 hSF hMG,
    gcd_eq_one_of_dvd_seven_of_not_left hc.2.2 hSF,
    (Nat.coprime_iff_gcd_eq_one.mp hrep)⟩

theorem GNCubicPaired_swapSevenDeep_crossGcd_packet {a : ℕ}
    (ha : 0 < a) (ha49 : a % 49 = 22) :
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) = 7 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNCubicSwapRepeatedPart a) = 1 := by
  have hs := GNCubicPaired_swapSevenDeep_packet ha ha49
  rcases hs with ⟨hF7, hG7, hF49, hG49, hMF, hMG, hSF, hSG⟩
  have hc := GNCubicPaired_cross_gcd_packet ha
  have hrep := GNCubicPairedRepeatedParts_coprime ha
  exact ⟨gcd_eq_one_of_dvd_seven_of_not_both hc.1 hMF hSG,
    gcd_eq_seven_of_dvd_seven hc.2.1 hSF hMG,
    gcd_eq_one_of_dvd_seven_of_not_right hc.2.2 hSG,
    (Nat.coprime_iff_gcd_eq_one.mp hrep)⟩

theorem GNCubicPaired_shallowSeven_crossGcd_packet {a : ℕ}
    (ha : 0 < a) (ha7 : a % 7 = 1)
    (h29 : a % 49 ≠ 29) (h22 : a % 49 ≠ 22) :
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) = 7 ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNCubicSwapRepeatedPart a) = 1 := by
  have hs := GNCubicPaired_shallowSeven_packet ha ha7 h29 h22
  rcases hs with ⟨hF7, hG7, hF49, hG49, hMF, hMG, hSF, hSG⟩
  have hc := GNCubicPaired_cross_gcd_packet ha
  have hrep := GNCubicPairedRepeatedParts_coprime ha
  exact ⟨gcd_eq_one_of_dvd_seven_of_not_left hc.1 hMF,
    gcd_eq_one_of_dvd_seven_of_not_right hc.2.1 hMG,
    gcd_eq_seven_of_dvd_seven hc.2.2 hSF hSG,
    (Nat.coprime_iff_gcd_eq_one.mp hrep)⟩

theorem seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState {a : ℕ}
    (_ha : 0 < a) (ha7 : a % 7 = 1) :
    7 ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a ↔
      a % 49 = 29 ∨ a % 49 = 22 := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with hF | hG
    · left
      exact (fortyNine_dvd_GNCubicForwardValue_iff_mod_eq_twentyNine ha7).mp
        ((seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value a).mp hF)
    · right
      exact (fortyNine_dvd_GNCubicSwapValue_iff_mod_eq_twentyTwo ha7).mp
        ((seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value a).mp hG)
  · intro h
    rcases h with h | h
    · apply dvd_mul_of_dvd_left
      exact (seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value a).mpr
        ((fortyNine_dvd_GNCubicForwardValue_iff_mod_eq_twentyNine ha7).mpr h)
    · apply dvd_mul_of_dvd_right
      exact (seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value a).mpr
        ((fortyNine_dvd_GNCubicSwapValue_iff_mod_eq_twentyTwo ha7).mpr h)

theorem fortyNine_dvd_GNCubicPairedRepeatedProduct_iff_deepState {a : ℕ}
    (ha : 0 < a) (ha7 : a % 7 = 1) :
    49 ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a ↔
      a % 49 = 29 ∨ a % 49 = 22 := by
  constructor
  · intro h
    apply (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState ha ha7).mp
    exact dvd_trans (dvd_pow_self 7 (by norm_num : (2 : ℕ) ≠ 0)) h
  · intro h
    have h7 := (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState ha ha7).mpr h
    exact GNCubicPairedRepeatedProduct_prime_sq_dvd ha (by norm_num) h7

theorem GNCubicPaired_sevenDepth_cases {a : ℕ} (_ha7 : a % 7 = 1) :
    a % 49 = 29 ∨ a % 49 = 22 ∨
      (a % 49 ≠ 29 ∧ a % 49 ≠ 22) := by
  by_cases h29 : a % 49 = 29
  · exact Or.inl h29
  by_cases h22 : a % 49 = 22
  · exact Or.inr (Or.inl h22)
  · exact Or.inr (Or.inr ⟨h29, h22⟩)

end DkMath.ABC
