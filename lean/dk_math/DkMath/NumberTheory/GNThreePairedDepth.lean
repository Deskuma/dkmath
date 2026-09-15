/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GNThreeHenselDepth
import Mathlib.Data.Nat.ModEq

open DkMath.CosmicFormulaBinom
#print "file: DkMath.NumberTheory.GNThreePairedDepth"

/-!
# Independent exact cubic orientation depths

Finite simple-root lifting and CRT give arithmetic progressions with two
independently prescribed exact depths. This proves compatibility, not a
height-relative density bound or an ABC statement.
-/

namespace DkMath.NumberTheory

/-- Cubic GN respects simultaneous congruence of its natural coordinates. -/
theorem GN_three_modEq {m a b u v : ℕ}
    (ha : a ≡ u [MOD m]) (hb : b ≡ v [MOD m]) :
    GN 3 a b ≡ GN 3 u v [MOD m] := by
  simp only [GN_three_dual_explicit]
  exact ((ha.pow 2).add (((ha.mul_left 3).mul hb))).add ((hb.pow 2).mul_left 3)

/-- A nonramified unit-boundary seed extends to every finite positive depth. -/
theorem exists_GN_three_unit_pow_root {q r : ℕ}
    (hq : Nat.Prime q) (hq3 : q ≠ 3) (hr : q ∣ GN 3 r 1)
    (k : ℕ) : ∃ u : ℕ, q ^ (k + 1) ∣ GN 3 u 1 := by
  induction k with
  | zero => exact ⟨r, by simpa using hr⟩
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨t, ht, _⟩ := existsUnique_GN_three_powLift_digit_of_primitive_nonramified
      hq (by omega : 1 ≤ k + 1) (by simp : Nat.Coprime u 1) hq3 hu
    exact ⟨u + q ^ (k + 1) * (t : ℕ), ht⟩

/-- Departing a lifted simple root by one depth-sized step gives exact depth. -/
theorem exists_GN_three_unit_exact_depth {q r : ℕ}
    (hq : Nat.Prime q) (hq3 : q ≠ 3) (hr : q ∣ GN 3 r 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ u : ℕ, q ^ k ∣ GN 3 u 1 ∧ ¬ q ^ (k + 1) ∣ GN 3 u 1 := by
  obtain ⟨u, hu⟩ := exists_GN_three_unit_pow_root hq hq3 hr k
  have hsmall : q ^ k ∣ GN 3 u 1 := (pow_dvd_pow q (by omega : k ≤ k+1)).trans hu
  have hqGN : q ∣ GN 3 u 1 := (dvd_pow_self q (by omega : k ≠ 0)).trans hsmall
  have hder := prime_not_dvd_cubic_boundary_derivative hq (by simp : Nat.Coprime u 1) hqGN hq3
  have hcong : u + q ^ k * 1 ≡ u [MOD q ^ k] := by simp [Nat.ModEq]
  refine ⟨u + q ^ k * 1, ((GN_three_modEq hcong (Nat.ModEq.refl 1)).dvd_iff (dvd_refl _)).mpr hsmall, ?_⟩
  intro hbad
  have hlin := (pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff hq.pos hk hsmall).mp hbad
  have hquot : q ∣ GN 3 u 1 / q ^ k := by
    apply Nat.dvd_of_mul_dvd_mul_left (pow_pos hq.pos k)
    rw [Nat.mul_div_cancel' hsmall, ← pow_succ]
    exact hu
  have h := (Nat.dvd_add_iff_right hquot).mpr hlin
  exact hder (by simpa using h)

/-- Scaling by three exchanges which coordinate varies in the cubic shell. -/
theorem GN_three_three_mul_unit (u : ℕ) : GN 3 (3*u) 1 = 3 * GN 3 1 u := by
  simp only [GN_three_dual_explicit]
  ring

/-- Exact first-coordinate roots give exact roots in the opposite orientation. -/
theorem exists_GN_three_swapped_unit_exact_depth {q r : ℕ}
    (hq : Nat.Prime q) (hq3 : q ≠ 3) (hqcop : Nat.Coprime q 3)
    (hr : q ∣ GN 3 r 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ u : ℕ, q ^ k ∣ GN 3 1 u ∧ ¬ q ^ (k + 1) ∣ GN 3 1 u := by
  obtain ⟨u, hu, hun⟩ := exists_GN_three_unit_exact_depth hq hq3 hr hk
  let z := Nat.chineseRemainder (hqcop.pow_left (k+1)) u 0
  have hz3 : 3 ∣ (z : ℕ) := Nat.modEq_zero_iff_dvd.mp z.property.2
  obtain ⟨v,hv⟩ := hz3
  have hcong := GN_three_modEq z.property.1 (Nat.ModEq.refl 1)
  rw [hv, GN_three_three_mul_unit] at hcong
  refine ⟨v, ?_, ?_⟩
  · exact (hqcop.pow_left k).dvd_of_dvd_mul_left
      ((hcong.dvd_iff (pow_dvd_pow q (by omega : k ≤ k+1))).mpr hu)
  · intro hbad
    exact hun ((hcong.dvd_iff (dvd_refl _)).mp (dvd_mul_of_dvd_right hbad 3))

/-- Independent exact depths persist along a paired CRT progression. -/
theorem exists_GN_three_pair_exact_depth_progression
    {q r u v k l : ℕ} (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hq3 : q ≠ 3) (hr3 : r ≠ 3) (hrcop : Nat.Coprime r 3)
    (hqr : Nat.Coprime q r) (hu : q ∣ GN 3 u 1) (hv : r ∣ GN 3 v 1)
    (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∃ a₀ : ℕ, a₀ < q^(k+1)*r^(l+1) ∧ ∀ t : ℕ,
      let a := a₀ + q^(k+1)*r^(l+1)*t
      q^k ∣ GN 3 a 1 ∧ ¬ q^(k+1) ∣ GN 3 a 1 ∧
      r^l ∣ GN 3 1 a ∧ ¬ r^(l+1) ∣ GN 3 1 a := by
  obtain ⟨x, hx, hxn⟩ := exists_GN_three_unit_exact_depth hq hq3 hu hk
  obtain ⟨y, hy, hyn⟩ := exists_GN_three_swapped_unit_exact_depth hr hr3 hrcop hv hl
  let z := Nat.chineseRemainder (hqr.pow (k+1) (l+1)) x y
  refine ⟨z, Nat.chineseRemainder_lt_mul _ _ _ (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hr.ne_zero), ?_⟩
  intro t
  dsimp only
  have hzm : (z:ℕ) + q^(k+1)*r^(l+1)*t ≡ (z:ℕ) [MOD q^(k+1)*r^(l+1)] := by
    simp [Nat.ModEq]
  have hqz := (hzm.of_dvd (dvd_mul_right (q^(k+1)) (r^(l+1)))).trans z.property.1
  have hrz := (hzm.of_dvd (dvd_mul_left (r^(l+1)) (q^(k+1)))).trans z.property.2
  have hF := GN_three_modEq hqz (Nat.ModEq.refl 1)
  have hG := GN_three_modEq (Nat.ModEq.refl 1) hrz
  exact ⟨(hF.dvd_iff (pow_dvd_pow q (by omega : k ≤ k+1))).mpr hx,
    fun h => hxn ((hF.dvd_iff (dvd_refl _)).mp h),
    (hG.dvd_iff (pow_dvd_pow r (by omega : l ≤ l+1))).mpr hy,
    fun h => hyn ((hG.dvd_iff (dvd_refl _)).mp h)⟩

/-- The primes 7 and 13 realize every pair of positive exact depths. -/
theorem exists_GN_three_seven_thirteen_exact_depth_progression {k l : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∃ a₀ : ℕ, a₀ < 7^(k+1)*13^(l+1) ∧ ∀ t : ℕ,
      let a := a₀ + 7^(k+1)*13^(l+1)*t
      7^k ∣ GN 3 a 1 ∧ ¬ 7^(k+1) ∣ GN 3 a 1 ∧
      13^l ∣ GN 3 1 a ∧ ¬ 13^(l+1) ∣ GN 3 1 a := by
  apply exists_GN_three_pair_exact_depth_progression (u := 1) (v := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  · rw [GN_three_dual_explicit]; norm_num
  · rw [GN_three_dual_explicit]; norm_num
  · exact hk
  · exact hl

/-- Exact paired depths occur beyond every prescribed height on coprime coordinates. -/
theorem exists_large_GN_three_seven_thirteen_exact_depth {k l : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) (L : ℕ) :
    ∃ a : ℕ, L < a ∧ Nat.Coprime a 1 ∧
      7^k ∣ GN 3 a 1 ∧ ¬ 7^(k+1) ∣ GN 3 a 1 ∧
      13^l ∣ GN 3 1 a ∧ ¬ 13^(l+1) ∣ GN 3 1 a := by
  obtain ⟨a₀, _, ha⟩ := exists_GN_three_seven_thirteen_exact_depth_progression hk hl
  refine ⟨a₀ + 7^(k+1)*13^(l+1)*(L+1), ?_, by simp, ha (L+1)⟩
  have hP : 1 ≤ (7:ℕ)^(k+1)*13^(l+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h := Nat.mul_le_mul_right (L+1) hP
  omega

end DkMath.NumberTheory
