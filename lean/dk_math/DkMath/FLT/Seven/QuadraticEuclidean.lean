/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticResidualPacket
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.EuclideanDomain

#print "file: DkMath.FLT.Seven.QuadraticEuclidean"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

theorem traceOneNegTwo_eq_zero_or_eq_zero_of_mul_eq_zero
    {x y : TraceOneInt (-2)} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have hnorm : tqNorm x * tqNorm y = 0 := by
    rw [← traceOne_norm_mul, h]
    rfl
  rcases mul_eq_zero.mp hnorm with hx | hy
  · exact Or.inl ((norm_eq_zero_iff_of_negTwo x).mp hx)
  · exact Or.inr ((norm_eq_zero_iff_of_negTwo y).mp hy)

instance traceOneNegTwoNoZeroDivisors : NoZeroDivisors (TraceOneInt (-2)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := traceOneNegTwo_eq_zero_or_eq_zero_of_mul_eq_zero

instance traceOneNegTwoNontrivial : Nontrivial (TraceOneInt (-2)) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have := congrArg TraceOneInt.fst h
  norm_num at this

instance traceOneNegTwoIsDomain : IsDomain (TraceOneInt (-2)) where

/-- Rational coordinates in the integral basis `1, tau`. -/
abbrev SevenRat := ℚ × ℚ

def sevenRatNorm (x : SevenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 + 2 * x.2 ^ 2

theorem sevenRatNorm_completed_square (u v : ℚ) :
    sevenRatNorm (u, v) =
      (u + v / 2) ^ 2 + (7 / 4 : ℚ) * v ^ 2 := by
  simp [sevenRatNorm]
  ring

theorem sevenRatNorm_le_eleven_sixteen
    {u v : ℚ} (hv : |v| ≤ (1 : ℚ) / 2)
    (hu : |u + v / 2| ≤ (1 : ℚ) / 2) :
    sevenRatNorm (u, v) ≤ (11 : ℚ) / 16 := by
  have hv' := abs_le.mp hv
  have hu' := abs_le.mp hu
  rw [sevenRatNorm_completed_square]
  nlinarith [sq_nonneg v, sq_nonneg (u + v / 2)]

theorem sevenRatNorm_lt_one
    {u v : ℚ} (hv : |v| ≤ (1 : ℚ) / 2)
    (hu : |u + v / 2| ≤ (1 : ℚ) / 2) :
    sevenRatNorm (u, v) < 1 := by
  have h := sevenRatNorm_le_eleven_sixteen hv hu
  norm_num at h ⊢
  linarith

theorem sevenRatNorm_nonneg (u v : ℚ) : 0 ≤ sevenRatNorm (u, v) := by
  rw [sevenRatNorm_completed_square]
  positivity

def sevenQuotientNumerator
    (x y : TraceOneInt (-2)) : TraceOneInt (-2) := x * conj y

theorem sevenQuotientNumerator_fst (x y : TraceOneInt (-2)) :
    (sevenQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) + 2 * x.snd * y.snd := by
  simp [sevenQuotientNumerator, conj]

theorem sevenQuotientNumerator_snd (x y : TraceOneInt (-2)) :
    (sevenQuotientNumerator x y).snd =
      x.snd * y.fst - x.fst * y.snd := by
  simp [sevenQuotientNumerator, conj]
  ring

def sevenQuotientCoords (x y : TraceOneInt (-2)) : SevenRat :=
  (((sevenQuotientNumerator x y).fst : ℚ) / tqNorm y,
    ((sevenQuotientNumerator x y).snd : ℚ) / tqNorm y)

def sevenRoundedSnd (x y : TraceOneInt (-2)) : ℤ :=
  round (sevenQuotientCoords x y).2

def sevenRoundedFst (x y : TraceOneInt (-2)) : ℤ :=
  let B := (sevenQuotientCoords x y).2
  let n := sevenRoundedSnd x y
  round ((sevenQuotientCoords x y).1 + (B - n) / 2)

def sevenQuotient (x y : TraceOneInt (-2)) : TraceOneInt (-2) :=
  ⟨sevenRoundedFst x y, sevenRoundedSnd x y⟩

def sevenRemainder (x y : TraceOneInt (-2)) : TraceOneInt (-2) :=
  x - sevenQuotient x y * y

theorem sevenQuotient_zero (x : TraceOneInt (-2)) : sevenQuotient x 0 = 0 := by
  ext <;> simp [sevenQuotient, sevenRoundedFst, sevenRoundedSnd,
    sevenQuotientCoords, sevenQuotientNumerator, conj,
    DkMath.NumberTheory.TraceOneQuadratic.norm]

theorem seven_quotient_mul_add_remainder
    (x y : TraceOneInt (-2)) :
    y * sevenQuotient x y + sevenRemainder x y = x := by
  simp [sevenRemainder]
  ring

def sevenEuclideanSize (x : TraceOneInt (-2)) : ℕ := Int.natAbs (tqNorm x)

theorem sevenEuclideanSize_pos_of_ne_zero
    {x : TraceOneInt (-2)} (hx : x ≠ 0) : 0 < sevenEuclideanSize x := by
  rw [sevenEuclideanSize, Int.natAbs_pos]
  exact fun hn => hx ((norm_eq_zero_iff_of_negTwo x).mp hn)

theorem sevenEuclideanSize_mul (x y : TraceOneInt (-2)) :
    sevenEuclideanSize (x * y) = sevenEuclideanSize x * sevenEuclideanSize y := by
  change (tqNorm (x * y)).natAbs = (tqNorm x).natAbs * (tqNorm y).natAbs
  rw [traceOne_norm_mul, Int.natAbs_mul]

theorem traceOneNegTwo_norm_nonneg (x : TraceOneInt (-2)) : 0 ≤ tqNorm x := by
  rcases x with ⟨a, b⟩
  rw [traceOneNorm_neg_two]
  nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]

private theorem sevenRemainder_norm_rat_identity
    (x y : TraceOneInt (-2)) (hy : y ≠ 0) :
    (tqNorm (sevenRemainder x y) : ℚ) =
      (tqNorm y : ℚ) *
        sevenRatNorm
          ((sevenQuotientCoords x y).1 - (sevenQuotient x y).fst,
           (sevenQuotientCoords x y).2 - (sevenQuotient x y).snd) := by
  have hn : (tqNorm y : ℚ) ≠ 0 := by
    exact_mod_cast fun h => hy ((norm_eq_zero_iff_of_negTwo y).mp h)
  have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd + 2 * y.snd ^ 2 ≠ 0 := by
    simpa [DkMath.NumberTheory.TraceOneQuadratic.norm] using hn
  let A : ℚ := (sevenQuotientCoords x y).1
  let B : ℚ := (sevenQuotientCoords x y).2
  let m : ℤ := (sevenQuotient x y).fst
  let n : ℤ := (sevenQuotient x y).snd
  have hx1 : (x.fst : ℚ) = y.fst * A - 2 * y.snd * B := by
    dsimp [A, B, sevenQuotientCoords]
    rw [sevenQuotientNumerator_fst, sevenQuotientNumerator_snd]
    field_simp [hn']
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    ring
  have hx2 : (x.snd : ℚ) = y.snd * A + y.fst * B + y.snd * B := by
    dsimp [A, B, sevenQuotientCoords]
    rw [sevenQuotientNumerator_fst, sevenQuotientNumerator_snd]
    field_simp [hn']
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    ring
  have hr1 : ((sevenRemainder x y).fst : ℚ) =
      y.fst * (A - m) - 2 * y.snd * (B - n) := by
    simp only [sevenRemainder, fst_sub, fst_mul, Int.cast_sub, Int.cast_add,
      Int.cast_mul, m, n]
    rw [hx1]
    ring
  have hr2 : ((sevenRemainder x y).snd : ℚ) =
      y.snd * (A - m) + y.fst * (B - n) + y.snd * (B - n) := by
    simp only [sevenRemainder, snd_sub, snd_mul, Int.cast_sub, Int.cast_add,
      Int.cast_mul, m, n]
    rw [hx2]
    ring
  dsimp only [DkMath.NumberTheory.TraceOneQuadratic.norm, sevenRatNorm]
  push_cast
  change _ = _ * ((A - (m : ℚ)) ^ 2 + (A - (m : ℚ)) * (B - (n : ℚ)) +
    2 * (B - (n : ℚ)) ^ 2)
  rw [hr1, hr2]
  ring

theorem sevenRoundedSnd_error_bound (x y : TraceOneInt (-2)) :
    |(sevenQuotientCoords x y).2 - sevenRoundedSnd x y| ≤ (1 : ℚ) / 2 := by
  exact abs_sub_round (sevenQuotientCoords x y).2

theorem sevenRoundedFst_skew_error_bound (x y : TraceOneInt (-2)) :
    |((sevenQuotientCoords x y).1 - sevenRoundedFst x y) +
      ((sevenQuotientCoords x y).2 - sevenRoundedSnd x y) / 2| ≤
        (1 : ℚ) / 2 := by
  let A := (sevenQuotientCoords x y).1
  let B := (sevenQuotientCoords x y).2
  let n := sevenRoundedSnd x y
  have h := abs_sub_round (A + (B - n) / 2)
  dsimp [sevenRoundedFst, A, B, n] at h ⊢
  convert h using 1
  all_goals first | rfl | ring_nf

theorem seven_remainder_size_lt
    (x : TraceOneInt (-2)) {y : TraceOneInt (-2)} (hy : y ≠ 0) :
    sevenEuclideanSize (sevenRemainder x y) < sevenEuclideanSize y := by
  let A := (sevenQuotientCoords x y).1
  let B := (sevenQuotientCoords x y).2
  let m := sevenRoundedFst x y
  let n := sevenRoundedSnd x y
  have hv : |B - n| ≤ (1 : ℚ) / 2 := sevenRoundedSnd_error_bound x y
  have hu : |(A - m) + (B - n) / 2| ≤ (1 : ℚ) / 2 :=
    sevenRoundedFst_skew_error_bound x y
  have hcell : sevenRatNorm (A - m, B - n) < 1 :=
    sevenRatNorm_lt_one hv hu
  have hnpos : 0 < (tqNorm y : ℚ) := by
    exact_mod_cast one_le_traceOneNorm_negTwo_of_ne_zero y hy
  have hid := sevenRemainder_norm_rat_identity x y hy
  have hrat : (tqNorm (sevenRemainder x y) : ℚ) < (tqNorm y : ℚ) := by
    rw [hid]
    have := mul_lt_mul_of_pos_left hcell hnpos
    simpa [A, B, m, n, sevenQuotient] using this
  have hInt : tqNorm (sevenRemainder x y) < tqNorm y := by exact_mod_cast hrat
  change (tqNorm (sevenRemainder x y)).natAbs < (tqNorm y).natAbs
  rw [← Int.ofNat_lt]
  simpa only [Int.natAbs_of_nonneg
    (traceOneNegTwo_norm_nonneg (sevenRemainder x y)),
    Int.natAbs_of_nonneg (traceOneNegTwo_norm_nonneg y)] using hInt

noncomputable instance traceOneNegTwoEuclideanDomain :
    EuclideanDomain (TraceOneInt (-2)) where
  quotient := sevenQuotient
  quotient_zero := sevenQuotient_zero
  remainder := sevenRemainder
  quotient_mul_add_remainder_eq := seven_quotient_mul_add_remainder
  r := fun a b => sevenEuclideanSize a < sevenEuclideanSize b
  r_wellFounded := (measure sevenEuclideanSize).wf
  remainder_lt := seven_remainder_size_lt
  mul_left_not_lt := by
    intro a b hb
    apply not_lt_of_ge
    rw [sevenEuclideanSize_mul]
    have hbSize : 1 ≤ sevenEuclideanSize b :=
      sevenEuclideanSize_pos_of_ne_zero hb
    exact Nat.le_mul_of_pos_right _ hbSize

end DkMath.FLT.Seven
