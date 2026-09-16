/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinConjugateCoprime
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.EuclideanDomain

#print "file: DkMath.FLT.Three.EisensteinEuclidean"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Norm-Euclidean structure on the Eisenstein order

The concrete ring `TraceOneInt (-1)` is treated separately from the generic
trace-one family.  The quotient is obtained by skew nearest-integer rounding
in rational coordinates, and the positive-definite norm gives the Euclidean
size.
-/

/-- The positive-definite Eisenstein norm vanishes exactly at zero. -/
theorem eisenstein_norm_eq_zero_iff (x : EisensteinInt) :
    norm x = 0 ↔ x = 0 := by
  rcases x with ⟨r, s⟩
  change norm (eisensteinCoord r s) = 0 ↔ (eisensteinCoord r s : EisensteinInt) = 0
  rw [eisenstein_norm_coords]
  constructor
  · intro h
    have hsq : (2 * r + s) ^ 2 + 3 * s ^ 2 = 0 := by
      nlinarith
    have hs : s = 0 := by
      nlinarith [sq_nonneg (2 * r + s), sq_nonneg s]
    subst s
    have hr : r = 0 := by
      nlinarith [sq_nonneg r]
    subst r
    rfl
  · intro h
    have hr := congrArg TraceOneInt.fst h
    have hs := congrArg TraceOneInt.snd h
    have hr' : r = 0 := by simpa [eisensteinCoord] using hr
    have hs' : s = 0 := by simpa [eisensteinCoord] using hs
    simp [hr', hs']

theorem traceOneNegOne_eq_zero_or_eq_zero_of_mul_eq_zero
    {x y : TraceOneInt (-1)} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have hnorm : norm x * norm y = 0 := by
    rw [← traceOne_norm_mul, h]
    rfl
  rcases mul_eq_zero.mp hnorm with hx | hy
  · exact Or.inl ((eisenstein_norm_eq_zero_iff x).mp hx)
  · exact Or.inr ((eisenstein_norm_eq_zero_iff y).mp hy)

instance traceOneNegOneNoZeroDivisors : NoZeroDivisors (TraceOneInt (-1)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := traceOneNegOne_eq_zero_or_eq_zero_of_mul_eq_zero

instance traceOneNegOneNontrivial : Nontrivial (TraceOneInt (-1)) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hf := congrArg TraceOneInt.fst h
  norm_num at hf

instance traceOneNegOneIsDomain : IsDomain (TraceOneInt (-1)) where

/-- Rational coordinates for the concrete Eisenstein order. -/
abbrev EisensteinRat := ℚ × ℚ

def eisensteinRatNorm (x : EisensteinRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2

theorem eisensteinRatNorm_completed_square (u v : ℚ) :
    eisensteinRatNorm (u, v) =
      (u + v / 2) ^ 2 + (3 / 4 : ℚ) * v ^ 2 := by
  simp [eisensteinRatNorm]
  ring

theorem eisensteinRatNorm_le_seven_sixteen
    {u v : ℚ} (hv : |v| ≤ (1 : ℚ) / 2)
    (hu : |u + v / 2| ≤ (1 : ℚ) / 2) :
    eisensteinRatNorm (u, v) ≤ (7 : ℚ) / 16 := by
  have hv' := abs_le.mp hv
  have hu' := abs_le.mp hu
  rw [eisensteinRatNorm_completed_square]
  nlinarith [sq_nonneg v, sq_nonneg (u + v / 2)]

theorem eisensteinRatNorm_lt_one
    {u v : ℚ} (hv : |v| ≤ (1 : ℚ) / 2)
    (hu : |u + v / 2| ≤ (1 : ℚ) / 2) :
    eisensteinRatNorm (u, v) < 1 := by
  have h := eisensteinRatNorm_le_seven_sixteen hv hu
  norm_num at h ⊢
  linarith

theorem eisensteinRatNorm_nonneg (u v : ℚ) :
    0 ≤ eisensteinRatNorm (u, v) := by
  rw [eisensteinRatNorm_completed_square]
  positivity

/-- The conjugate-product numerator used for division. -/
def eisensteinQuotientNumerator
    (x y : EisensteinInt) : EisensteinInt := x * conj y

theorem eisensteinQuotientNumerator_fst (x y : EisensteinInt) :
    (eisensteinQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) + x.snd * y.snd := by
  simp [eisensteinQuotientNumerator, conj]

theorem eisensteinQuotientNumerator_snd (x y : EisensteinInt) :
    (eisensteinQuotientNumerator x y).snd =
      x.snd * y.fst - x.fst * y.snd := by
  simp [eisensteinQuotientNumerator, conj]
  ring

/-- Rational coordinates of `x / y`, represented by `x * conj y / N(y)`. -/
def eisensteinQuotientCoords (x y : EisensteinInt) : EisensteinRat :=
  (((eisensteinQuotientNumerator x y).fst : ℚ) / norm y,
    ((eisensteinQuotientNumerator x y).snd : ℚ) / norm y)

def eisensteinRoundedSnd (x y : EisensteinInt) : ℤ :=
  round (eisensteinQuotientCoords x y).2

def eisensteinRoundedFst (x y : EisensteinInt) : ℤ :=
  let B := (eisensteinQuotientCoords x y).2
  let n := eisensteinRoundedSnd x y
  round ((eisensteinQuotientCoords x y).1 + (B - n) / 2)

def eisensteinQuotient (x y : EisensteinInt) : EisensteinInt :=
  ⟨eisensteinRoundedFst x y, eisensteinRoundedSnd x y⟩

def eisensteinRemainder (x y : EisensteinInt) : EisensteinInt :=
  x - eisensteinQuotient x y * y

theorem eisensteinQuotient_zero (x : EisensteinInt) :
    eisensteinQuotient x 0 = 0 := by
  ext <;> simp [eisensteinQuotient, eisensteinRoundedFst,
    eisensteinRoundedSnd, eisensteinQuotientCoords,
    eisensteinQuotientNumerator, conj,
    DkMath.NumberTheory.TraceOneQuadratic.norm]

theorem eisenstein_quotient_mul_add_remainder
    (x y : EisensteinInt) :
    y * eisensteinQuotient x y + eisensteinRemainder x y = x := by
  simp [eisensteinRemainder]
  ring

def eisensteinEuclideanSize (x : EisensteinInt) : ℕ :=
  Int.natAbs (norm x)

theorem eisensteinEuclideanSize_pos_of_ne_zero
    {x : EisensteinInt} (hx : x ≠ 0) :
    0 < eisensteinEuclideanSize x := by
  rw [eisensteinEuclideanSize, Int.natAbs_pos]
  exact fun hn => hx ((eisenstein_norm_eq_zero_iff x).mp hn)

theorem eisensteinEuclideanSize_mul (x y : EisensteinInt) :
    eisensteinEuclideanSize (x * y) =
      eisensteinEuclideanSize x * eisensteinEuclideanSize y := by
  change (norm (x * y)).natAbs = (norm x).natAbs * (norm y).natAbs
  rw [traceOne_norm_mul, Int.natAbs_mul]

/-- Nonnegativity of the concrete Eisenstein norm. -/
theorem traceOneNegOne_norm_nonneg (x : EisensteinInt) : 0 ≤ norm x := by
  exact eisenstein_norm_nonneg x

private theorem eisensteinRemainder_norm_rat_identity
    (x y : EisensteinInt) (hy : y ≠ 0) :
    (norm (eisensteinRemainder x y) : ℚ) =
      (norm y : ℚ) *
        eisensteinRatNorm
          ((eisensteinQuotientCoords x y).1 -
              (eisensteinQuotient x y).fst,
           (eisensteinQuotientCoords x y).2 -
              (eisensteinQuotient x y).snd) := by
  have hn : (norm y : ℚ) ≠ 0 := by
    exact_mod_cast fun h => hy ((eisenstein_norm_eq_zero_iff y).mp h)
  have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd + y.snd ^ 2 ≠ 0 := by
    simpa [DkMath.NumberTheory.TraceOneQuadratic.norm] using hn
  let A : ℚ := (eisensteinQuotientCoords x y).1
  let B : ℚ := (eisensteinQuotientCoords x y).2
  let m : ℤ := (eisensteinQuotient x y).fst
  let n : ℤ := (eisensteinQuotient x y).snd
  have hx1 : (x.fst : ℚ) = y.fst * A - y.snd * B := by
    dsimp [A, B, eisensteinQuotientCoords]
    rw [eisensteinQuotientNumerator_fst,
      eisensteinQuotientNumerator_snd]
    field_simp [hn']
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    ring
  have hx2 : (x.snd : ℚ) = y.snd * A + y.fst * B + y.snd * B := by
    dsimp [A, B, eisensteinQuotientCoords]
    rw [eisensteinQuotientNumerator_fst,
      eisensteinQuotientNumerator_snd]
    field_simp [hn']
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    ring
  have hr1 : ((eisensteinRemainder x y).fst : ℚ) =
      y.fst * (A - m) - y.snd * (B - n) := by
    simp only [eisensteinRemainder, fst_sub, fst_mul,
      Int.cast_sub, Int.cast_add, Int.cast_mul, m, n]
    rw [hx1]
    ring
  have hr2 : ((eisensteinRemainder x y).snd : ℚ) =
      y.snd * (A - m) + y.fst * (B - n) + y.snd * (B - n) := by
    simp only [eisensteinRemainder, snd_sub, snd_mul,
      Int.cast_sub, Int.cast_add, Int.cast_mul, m, n]
    rw [hx2]
    ring
  dsimp only [DkMath.NumberTheory.TraceOneQuadratic.norm,
    eisensteinRatNorm]
  push_cast
  change _ = _ * ((A - (m : ℚ)) ^ 2 +
    (A - (m : ℚ)) * (B - (n : ℚ)) + (B - (n : ℚ)) ^ 2)
  rw [hr1, hr2]
  ring

theorem eisensteinRoundedSnd_error_bound (x y : EisensteinInt) :
    |(eisensteinQuotientCoords x y).2 - eisensteinRoundedSnd x y| ≤
      (1 : ℚ) / 2 := by
  exact abs_sub_round (eisensteinQuotientCoords x y).2

theorem eisensteinRoundedFst_skew_error_bound (x y : EisensteinInt) :
    |((eisensteinQuotientCoords x y).1 - eisensteinRoundedFst x y) +
      ((eisensteinQuotientCoords x y).2 - eisensteinRoundedSnd x y) / 2| ≤
        (1 : ℚ) / 2 := by
  let A := (eisensteinQuotientCoords x y).1
  let B := (eisensteinQuotientCoords x y).2
  let n := eisensteinRoundedSnd x y
  have h := abs_sub_round (A + (B - n) / 2)
  dsimp [eisensteinRoundedFst, A, B, n] at h ⊢
  convert h using 1
  all_goals first | rfl | ring_nf

theorem eisenstein_remainder_size_lt
    (x : EisensteinInt) {y : EisensteinInt} (hy : y ≠ 0) :
    eisensteinEuclideanSize (eisensteinRemainder x y) <
      eisensteinEuclideanSize y := by
  let A := (eisensteinQuotientCoords x y).1
  let B := (eisensteinQuotientCoords x y).2
  let m := eisensteinRoundedFst x y
  let n := eisensteinRoundedSnd x y
  have hv : |B - n| ≤ (1 : ℚ) / 2 :=
    eisensteinRoundedSnd_error_bound x y
  have hu : |(A - m) + (B - n) / 2| ≤ (1 : ℚ) / 2 :=
    eisensteinRoundedFst_skew_error_bound x y
  have hcell : eisensteinRatNorm (A - m, B - n) < 1 :=
    eisensteinRatNorm_lt_one hv hu
  have hnorm_pos : 0 < norm y := by
    have hnonneg : 0 ≤ norm y := eisenstein_norm_nonneg y
    have hne : norm y ≠ 0 := by
      intro h
      exact hy ((eisenstein_norm_eq_zero_iff y).mp h)
    omega
  have hnpos : 0 < (norm y : ℚ) := by
    exact_mod_cast hnorm_pos
  have hid := eisensteinRemainder_norm_rat_identity x y hy
  have hrat : (norm (eisensteinRemainder x y) : ℚ) < (norm y : ℚ) := by
    rw [hid]
    have hmul := mul_lt_mul_of_pos_left hcell hnpos
    simpa [A, B, m, n, eisensteinQuotient] using hmul
  have hInt : norm (eisensteinRemainder x y) < norm y := by
    exact_mod_cast hrat
  change (norm (eisensteinRemainder x y)).natAbs < (norm y).natAbs
  rw [← Int.ofNat_lt]
  simpa only [Int.natAbs_of_nonneg
    (traceOneNegOne_norm_nonneg (eisensteinRemainder x y)),
    Int.natAbs_of_nonneg (traceOneNegOne_norm_nonneg y)] using hInt

noncomputable instance traceOneNegOneEuclideanDomain :
    EuclideanDomain (TraceOneInt (-1)) where
  quotient := eisensteinQuotient
  quotient_zero := eisensteinQuotient_zero
  remainder := eisensteinRemainder
  quotient_mul_add_remainder_eq := eisenstein_quotient_mul_add_remainder
  r := fun a b => eisensteinEuclideanSize a < eisensteinEuclideanSize b
  r_wellFounded := (measure eisensteinEuclideanSize).wf
  remainder_lt := eisenstein_remainder_size_lt
  mul_left_not_lt := by
    intro a b hb
    apply not_lt_of_ge
    rw [eisensteinEuclideanSize_mul]
    have hbSize : 1 ≤ eisensteinEuclideanSize b :=
      eisensteinEuclideanSize_pos_of_ne_zero hb
    exact Nat.le_mul_of_pos_right _ hbSize

end DkMath.FLT.Three
