/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticBridge

#print "file: DkMath.FLT.Seven.AxisDivisibility"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- First coordinate of multiplication by the discriminant `-7` scale axis. -/
@[simp] theorem sevenAxis_mul_fst (c d : ℤ) :
    (sevenAxis * (⟨c, d⟩ : TraceOneInt (-2))).fst = -c - 4 * d := by
  rw [sevenAxis_eq]
  simp
  ring

/-- Second coordinate of multiplication by the discriminant `-7` scale axis. -/
@[simp] theorem sevenAxis_mul_snd (c d : ℤ) :
    (sevenAxis * (⟨c, d⟩ : TraceOneInt (-2))).snd = 2 * c + d := by
  rw [sevenAxis_eq]
  simp
  ring

/-- Divisibility by the scale axis is exactly divisibility of the trace by `7`. -/
theorem sevenAxis_dvd_iff_seven_dvd_trace (x : TraceOneInt (-2)) :
    sevenAxis ∣ x ↔ (7 : ℤ) ∣ trace x := by
  rcases x with ⟨a, b⟩
  constructor
  · rintro ⟨⟨c, d⟩, h⟩
    have hf := congrArg TraceOneInt.fst h
    have hs := congrArg TraceOneInt.snd h
    refine ⟨-d, ?_⟩
    simp [trace] at hf hs ⊢
    linear_combination 2 * hf + hs
  · rintro ⟨k, hk⟩
    refine ⟨(⟨4 * k - a, -k⟩ : TraceOneInt (-2)), ?_⟩
    apply traceOne_ext
    · simp
    · simp [trace] at hk ⊢
      linarith

/-- At discriminant `-7`, norm divisibility by `7` is equivalent to trace
divisibility by `7`. -/
theorem seven_dvd_norm_iff_seven_dvd_trace (x : TraceOneInt (-2)) :
    (7 : ℤ) ∣ tqNorm x ↔ (7 : ℤ) ∣ trace x := by
  rcases x with ⟨a, b⟩
  have hs := four_mul_traceOneNorm_negTwo_eq_sum_sq a b
  change (7 : ℤ) ∣ tqNorm (⟨a, b⟩ : TraceOneInt (-2)) ↔
    (7 : ℤ) ∣ trace (⟨a, b⟩ : TraceOneInt (-2))
  constructor
  · rintro ⟨k, hk⟩
    have hsq : (7 : ℤ) ∣ trace (⟨a, b⟩ : TraceOneInt (-2)) ^ 2 := by
      refine ⟨4 * k - b ^ 2, ?_⟩
      simp [trace] at hs ⊢
      nlinarith
    exact (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hsq
  · intro ht
    have hfour : (7 : ℤ) ∣ 4 * tqNorm (⟨a, b⟩ : TraceOneInt (-2)) := by
      have htraceSq : (7 : ℤ) ∣ trace (⟨a, b⟩ : TraceOneInt (-2)) ^ 2 :=
        dvd_pow ht (by norm_num : 2 ≠ 0)
      have hbSq : (7 : ℤ) ∣ 7 * b ^ 2 := dvd_mul_right 7 (b ^ 2)
      rw [hs]
      exact dvd_add htraceSq hbSq
    rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp hfour with h7four | hnorm
    · norm_num at h7four
    · exact hnorm

/-- The scale-axis and norm criteria are the same one-layer condition. -/
theorem sevenAxis_dvd_iff_seven_dvd_norm (x : TraceOneInt (-2)) :
    sevenAxis ∣ x ↔ (7 : ℤ) ∣ tqNorm x := by
  rw [sevenAxis_dvd_iff_seven_dvd_trace,
    seven_dvd_norm_iff_seven_dvd_trace]

/-- Removing one explicit scale-axis factor removes exactly one norm factor
`7`. -/
theorem norm_eq_seven_mul_norm_of_eq_sevenAxis_mul
    {x y : TraceOneInt (-2)} (hxy : x = sevenAxis * y) :
    tqNorm x = 7 * tqNorm y := by
  rw [hxy, traceOne_norm_mul, sevenAxis_norm]

/-- A nonzero element cannot be represented as the scale axis times zero. -/
theorem ne_zero_of_eq_sevenAxis_mul_of_ne_zero
    {x y : TraceOneInt (-2)} (hxy : x = sevenAxis * y) (hx : x ≠ 0) :
    y ≠ 0 := by
  intro hy
  subst y
  apply hx
  calc
    x = sevenAxis * 0 := hxy
    _ = 0 := mul_zero sevenAxis

/-- The residual factor after one explicit peel remains on a nonzero norm
shell. -/
theorem one_le_norm_of_eq_sevenAxis_mul_of_ne_zero
    {x y : TraceOneInt (-2)} (hxy : x = sevenAxis * y) (hx : x ≠ 0) :
    1 ≤ tqNorm y :=
  one_le_traceOneNorm_negTwo_of_ne_zero y
    (ne_zero_of_eq_sevenAxis_mul_of_ne_zero hxy hx)

/-- One explicit scale-axis peel strictly decreases the positive norm. -/
theorem norm_lt_of_eq_sevenAxis_mul_of_ne_zero
    {x y : TraceOneInt (-2)} (hxy : x = sevenAxis * y) (hx : x ≠ 0) :
    tqNorm y < tqNorm x := by
  rw [norm_eq_seven_mul_norm_of_eq_sevenAxis_mul hxy]
  have hy := one_le_norm_of_eq_sevenAxis_mul_of_ne_zero hxy hx
  nlinarith

/-- Exact endpoint-gap factorization of the trace of the seventh cyclotomic
coordinate package. -/
theorem trace_cyclotomicSevenToTraceOne (z y : ℤ) :
    trace (cyclotomicSevenToTraceOne z y) =
      (z - y) * (2 * (z - y) ^ 2 + 7 * z * y) := by
  simp [trace, cyclotomicSevenToTraceOne, cyclotomicSevenFst,
    cyclotomicSevenSnd]
  ring

/-- The seventh cyclotomic coordinate package contains one scale-axis factor
exactly when its endpoint gap is divisible by `7`. -/
theorem sevenAxis_dvd_cyclotomicSevenToTraceOne_iff (z y : ℤ) :
    sevenAxis ∣ cyclotomicSevenToTraceOne z y ↔ (7 : ℤ) ∣ z - y := by
  rw [sevenAxis_dvd_iff_seven_dvd_trace,
    trace_cyclotomicSevenToTraceOne]
  constructor
  · intro hprod
    rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp hprod with hgap | hfactor
    · exact hgap
    · have htwosq : (7 : ℤ) ∣ 2 * (z - y) ^ 2 := by
        convert dvd_sub hfactor (dvd_mul_right 7 (z * y)) using 1
        · rfl
        · rw [mul_assoc]
          simp
      rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp htwosq with htwo | hsq
      · norm_num at htwo
      · exact (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hsq
  · intro hgap
    exact dvd_mul_of_dvd_left hgap _

/-- The homogeneous seventh cyclotomic kernel is divisible by `7` exactly on
the endpoint-gap congruence class. -/
theorem seven_dvd_cyclotomicSeven_iff (z y : ℤ) :
    (7 : ℤ) ∣ cyclotomicSeven z y ↔ (7 : ℤ) ∣ z - y := by
  rw [cyclotomicSeven_eq_traceOneNorm_negTwo,
    seven_dvd_norm_iff_seven_dvd_trace,
    trace_cyclotomicSevenToTraceOne]
  constructor
  · intro hprod
    rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp hprod with hgap | hfactor
    · exact hgap
    · have htwosq : (7 : ℤ) ∣ 2 * (z - y) ^ 2 :=
        by
          convert dvd_sub hfactor (dvd_mul_right 7 (z * y)) using 1
          · rfl
          · rw [mul_assoc]
            simp
      rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp htwosq with htwo | hsq
      · norm_num at htwo
      · exact (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hsq
  · intro hgap
    exact dvd_mul_of_dvd_left hgap _

/-- Natural endpoint-gap form of the `GN 7` divisibility criterion. -/
theorem seven_dvd_GN_seven_sub_iff (a b : ℕ) (hab : b ≤ a) :
    7 ∣ GN 7 (a - b) b ↔ 7 ∣ a - b := by
  calc
    7 ∣ GN 7 (a - b) b ↔
        (7 : ℤ) ∣ ((GN 7 (a - b) b : ℕ) : ℤ) := Int.ofNat_dvd.symm
    _ ↔ (7 : ℤ) ∣ tqNorm (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ)) := by
      rw [GN_seven_sub_eq_traceOneNorm_negTwo a b hab]
    _ ↔ (7 : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
      rw [← cyclotomicSeven_eq_traceOneNorm_negTwo,
        seven_dvd_cyclotomicSeven_iff]
    _ ↔ (7 : ℤ) ∣ ((a - b : ℕ) : ℤ) := by rw [Int.ofNat_sub hab]
    _ ↔ 7 ∣ a - b := Int.ofNat_dvd

end DkMath.FLT.Seven
