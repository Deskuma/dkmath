/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.AxisDivisibility

#print "file: DkMath.FLT.Seven.AxisPowerRoll"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Each finite power of the scale axis contributes the corresponding power
of `7` to the norm. -/
theorem norm_sevenAxis_pow (n : ℕ) :
    tqNorm (sevenAxis ^ n) = (7 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]
  | succ n ih =>
      rw [pow_succ, traceOne_norm_mul, ih, sevenAxis_norm, pow_succ]

/-- Exact norm scaling after removing an explicitly given finite axis power. -/
theorem norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hxy : x = sevenAxis ^ n * y) :
    tqNorm x = (7 : ℤ) ^ n * tqNorm y := by
  rw [hxy, traceOne_norm_mul, norm_sevenAxis_pow]

/-- Divisibility by a finite axis power is exactly divisibility of the norm by
the matching power of `7`. -/
theorem sevenAxis_pow_dvd_iff_pow_seven_dvd_norm
    (n : ℕ) (x : TraceOneInt (-2)) :
    sevenAxis ^ n ∣ x ↔ (7 : ℤ) ^ n ∣ tqNorm x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      constructor
      · rintro ⟨y, hxy⟩
        refine ⟨tqNorm y, ?_⟩
        rw [hxy, traceOne_norm_mul, norm_sevenAxis_pow]
      · rintro ⟨k, hk⟩
        have hsevenNorm : (7 : ℤ) ∣ tqNorm x := by
          refine ⟨(7 : ℤ) ^ n * k, ?_⟩
          rw [hk, pow_succ]
          ring
        rcases (sevenAxis_dvd_iff_seven_dvd_norm x).mpr hsevenNorm with ⟨y, hxy⟩
        have hnormPeel : tqNorm x = 7 * tqNorm y :=
          norm_eq_seven_mul_norm_of_eq_sevenAxis_mul hxy
        have hyNorm : (7 : ℤ) ^ n ∣ tqNorm y := by
          refine ⟨k, ?_⟩
          apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
          rw [← hnormPeel, hk, pow_succ]
          ring
        rcases (ih y).mpr hyNorm with ⟨z, hyz⟩
        refine ⟨z, ?_⟩
        rw [hxy, hyz, pow_succ]
        ring

/-- A nonzero element cannot have a zero quotient after an explicit finite
axis-power factorization. -/
theorem ne_zero_of_eq_sevenAxis_pow_mul_of_ne_zero
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hxy : x = sevenAxis ^ n * y) (hx : x ≠ 0) :
    y ≠ 0 := by
  intro hy
  subst y
  apply hx
  calc
    x = sevenAxis ^ n * 0 := hxy
    _ = 0 := mul_zero _

/-- The quotient left after finitely many explicit axis layers remains on a
positive integral norm shell. -/
theorem one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hxy : x = sevenAxis ^ n * y) (hx : x ≠ 0) :
    1 ≤ tqNorm y :=
  one_le_traceOneNorm_negTwo_of_ne_zero y
    (ne_zero_of_eq_sevenAxis_pow_mul_of_ne_zero hxy hx)

/-- A nonzero element containing `n` axis layers has norm at least `7^n`. -/
theorem pow_seven_le_norm_of_sevenAxis_pow_dvd
    {x : TraceOneInt (-2)} {n : ℕ}
    (hx : x ≠ 0) (hdiv : sevenAxis ^ n ∣ x) :
    (7 : ℤ) ^ n ≤ tqNorm x := by
  rcases hdiv with ⟨y, hxy⟩
  rw [norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul hxy]
  have hy := one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero hxy hx
  have hp : 0 ≤ (7 : ℤ) ^ n := pow_nonneg (by norm_num) n
  nlinarith

/-- Stable obstruction form of the finite-thickness bound. -/
theorem not_sevenAxis_pow_dvd_of_norm_lt_pow_seven
    {x : TraceOneInt (-2)} {n : ℕ}
    (hx : x ≠ 0) (hlt : tqNorm x < (7 : ℤ) ^ n) :
    ¬ sevenAxis ^ n ∣ x := by
  intro hdiv
  exact (not_le_of_gt hlt) (pow_seven_le_norm_of_sevenAxis_pow_dvd hx hdiv)

/-- Removing a positive number of axis layers strictly decreases the norm of
a nonzero element. -/
theorem norm_lt_of_eq_sevenAxis_pow_mul_of_ne_zero
    {x y : TraceOneInt (-2)} {n : ℕ}
    (hn : 0 < n) (hxy : x = sevenAxis ^ n * y) (hx : x ≠ 0) :
    tqNorm y < tqNorm x := by
  rw [norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul hxy]
  have hy := one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero hxy hx
  have hp : (2 : ℤ) ≤ (7 : ℤ) ^ n := by
    have hp' : (7 : ℤ) ^ 1 ≤ (7 : ℤ) ^ n :=
      pow_le_pow_right₀ (by norm_num) hn
    norm_num at hp' ⊢
    omega
  nlinarith

/-- Cyclotomic specialization of the finite axis-power/norm-power criterion. -/
theorem sevenAxis_pow_dvd_cyclotomicSevenToTraceOne_iff
    (n : ℕ) (z y : ℤ) :
    sevenAxis ^ n ∣ cyclotomicSevenToTraceOne z y ↔
      (7 : ℤ) ^ n ∣ cyclotomicSeven z y := by
  rw [sevenAxis_pow_dvd_iff_pow_seven_dvd_norm,
    ← cyclotomicSeven_eq_traceOneNorm_negTwo]

end DkMath.FLT.Seven
