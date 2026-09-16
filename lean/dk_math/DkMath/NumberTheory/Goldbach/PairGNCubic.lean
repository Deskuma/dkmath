/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.Goldbach.PairGN
import DkMath.NumberTheory.GNThreeQuadratic

/-! # Cubic and asymmetric unit-boundary GN pairs

The quadratic equations are exact, but representation is restrictive.
In particular, degrees (2,3) miss every center congruent to 8 modulo 9.
-/

namespace DkMath.NumberTheory.GoldbachPairGN

open DkMath.CosmicFormulaBinom

theorem cubic_unit (u : ℕ) : GN 3 1 u = 3 * u ^ 2 + 3 * u + 1 := by
  rw [GN_three_dual_explicit]
  ring

theorem cubic_unit_quotient (u : ℕ) : GN 3 1 u = 1 + 3 * (u * (u + 1)) := by
  rw [cubic_unit]
  ring

/-- The Beam quotient is pronic, not an arbitrary nonnegative integer. -/
theorem cubic_quotient_eq_iff (u A : ℕ) :
    GN 3 1 u = 1 + 3 * A ↔ A = u * (u + 1) := by
  rw [cubic_unit_quotient]
  omega

theorem pairBody_three_three_eq_iff {n u v : ℕ} (hn : 1 ≤ n) :
    pairBody 3 3 u v = 2 * n ↔
      2 * (n - 1) = 3 * (u * (u + 1) + v * (v + 1)) := by
  rw [pairBody, cubic_unit, cubic_unit]
  have hnsub : n - 1 + 1 = n := by omega
  constructor <;> intro h <;> nlinarith

/-- Subtraction-free completion of squares, valid also at n=0. -/
theorem pairBody_three_three_eq_iff_circle {n u v : ℕ} :
    pairBody 3 3 u v = 2 * n ↔
      8 * n = 3 * ((2 * u + 1) ^ 2 + (2 * v + 1) ^ 2) + 2 := by
  rw [pairBody, cubic_unit, cubic_unit]
  constructor <;> intro h <;> nlinarith

/-- The exact subtraction form in the proposed argument. -/
theorem pairBody_three_three_eq_iff_circle_sub {n u v : ℕ} (hn : 1 ≤ n) :
    pairBody 3 3 u v = 2 * n ↔
      8 * n - 2 = 3 * ((2 * u + 1) ^ 2 + (2 * v + 1) ^ 2) := by
  rw [pairBody_three_three_eq_iff_circle]
  omega

theorem center_mod_three_of_cubic_pair {n u v : ℕ}
    (h : pairBody 3 3 u v = 2 * n) : n % 3 = 1 := by
  rw [pairBody, cubic_unit, cubic_unit] at h
  omega

theorem pairBody_two_three_eq_iff {n u v : ℕ} (hn : 1 ≤ n) :
    pairBody 2 3 u v = 2 * n ↔
      2 * (n - 1) = 2 * u + 3 * v * (v + 1) := by
  rw [pairBody, goldbach_GN_two, cubic_unit]
  have hnsub : n - 1 + 1 = n := by omega
  constructor <;> intro h <;> nlinarith

/-- When n is 2 modulo 3, the quadratic-row prime on the left must be 3. -/
theorem mixed_left_parameter_eq_one {n u v : ℕ}
    (hn : n % 3 = 2) (hp : Nat.Prime (GN 2 1 u))
    (h : pairBody 2 3 u v = 2 * n) : u = 1 := by
  have heq := h
  rw [pairBody, goldbach_GN_two, cubic_unit] at heq
  have hdiv : 3 ∣ GN 2 1 u := by
    apply Nat.dvd_of_mod_eq_zero
    rw [goldbach_GN_two]
    omega
  have hthree : 3 = GN 2 1 u :=
    (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdiv
  rw [goldbach_GN_two] at hthree
  omega

/-- Complete mixed-row classification on the center class 2 modulo 3. -/
theorem unitPairAt_two_three_iff_on_mod_three {n : ℕ} (hn : n % 3 = 2) :
    UnitPairAt n 2 3 ↔
      ∃ v : ℕ, 0 < v ∧ Nat.Prime (GN 3 1 v) ∧ 2 * n = GN 3 1 v + 3 := by
  constructor
  · rintro ⟨u, v, _, hv, hp, hq, hsum⟩
    have hu := mixed_left_parameter_eq_one hn hp hsum
    refine ⟨v, hv, hq, ?_⟩
    rw [pairBody, goldbach_GN_two, hu] at hsum
    omega
  · rintro ⟨v, hv, hq, heq⟩
    refine ⟨1, v, by omega, hv, ?_, hq, ?_⟩
    · rw [goldbach_GN_two]
      norm_num
    · rw [pairBody, goldbach_GN_two]
      omega

theorem cubic_unit_mod_nine (v : ℕ) : GN 3 1 v % 9 = 1 ∨ GN 3 1 v % 9 = 7 := by
  rw [cubic_unit]
  have hv : v % 9 < 9 := Nat.mod_lt _ (by omega)
  interval_cases h : v % 9 <;> norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]

/-- Asymmetry (2,3) still excludes an entire arithmetic progression of centers. -/
theorem not_unitPairAt_two_three_of_mod_nine {n : ℕ} (hn : n % 9 = 8) :
    ¬ UnitPairAt n 2 3 := by
  intro h
  obtain ⟨v, _, _, heq⟩ := (unitPairAt_two_three_iff_on_mod_three (by omega : n % 3 = 2)).mp h
  have hres := cubic_unit_mod_nine v
  omega

theorem mixed_degrees_miss_progression (t : ℕ) : ¬ UnitPairAt (9 * t + 8) 2 3 := by
  apply not_unitPairAt_two_three_of_mod_nine
  omega

/-- A prime output with the required row congruence need not be in the cubic row. -/
theorem thirteen_not_in_cubic_row : ¬ ∃ v : ℕ, GN 3 1 v = 13 := by
  rintro ⟨v, hv⟩
  have hres := cubic_unit_mod_nine v
  rw [hv] at hres
  norm_num at hres

end DkMath.NumberTheory.GoldbachPairGN
