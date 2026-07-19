/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenDivisibility
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.EuclideanDomain

#print "file: DkMath.FLT.Five.GoldenEuclidean"

namespace DkMath.FLT.Five

/-- Rational coordinates in the basis `1, phi`. -/
abbrev GoldenRat := ℚ × ℚ

/-- The golden norm polynomial on rational coordinates. -/
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2

/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩

/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩

/--
The square fundamental cell is a strict golden-norm contraction cell.
The sharp uniform constant is `5/16`.
-/
theorem goldenRat_norm_abs_le_five_sixteen
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| ≤ (5 : ℚ) / 16 := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have huSq : u ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
  have hvSq : v ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
  rw [abs_le]
  constructor
  · have hs := sq_nonneg (u + v / 2)
    nlinarith
  · have hs := sq_nonneg (v - u / 2)
    nlinarith

theorem goldenRat_norm_abs_lt_one
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| < 1 := by
  have h := goldenRat_norm_abs_le_five_sixteen hu hv
  norm_num at h ⊢
  linarith

/-- A nonzero golden integer has nonzero norm. -/
theorem goldenNorm_ne_zero_of_ne_zero {y : GoldenInt} (hy : y ≠ 0) :
    goldenNorm y ≠ 0 := by
  intro hn
  have hm : goldenMul y (goldenConj y) = 0 := by
    rw [golden_mul_conj, hn]
    rfl
  rcases mul_eq_zero.mp hm with hy0 | hc0
  · exact hy hy0
  · apply hy
    rw [← goldenConj_invol y, hc0]
    rfl

/-- Numerator coordinates of `x * conjugate(y)`. -/
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)

theorem goldenQuotientNumerator_fst (x y : GoldenInt) :
    (goldenQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) - x.snd * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring

theorem goldenQuotientNumerator_snd (x y : GoldenInt) :
    (goldenQuotientNumerator x y).snd =
      x.snd * y.fst - x.fst * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring

/-- Rational coordinates of `x/y` in the golden basis. -/
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)

/-- The nearest integral golden quotient. -/
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩

/-- The residual after nearest-lattice normalization. -/
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y

theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]

theorem golden_quotient_mul_add_remainder (x y : GoldenInt) :
    y * goldenQuotient x y + goldenRemainder x y = x := by
  simp [goldenRemainder, golden_mul_eq]
  ring

/-- Euclidean size is the natural absolute value of the golden norm. -/
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)

theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx

theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]

private theorem goldenRemainder_norm_rat_identity
    (x y : GoldenInt) (hy : y ≠ 0) :
    (goldenNorm (goldenRemainder x y) : ℚ) =
      (goldenNorm y : ℚ) *
        goldenRatNorm
          ((goldenQuotientCoords x y).1 - (goldenQuotient x y).fst,
           (goldenQuotientCoords x y).2 - (goldenQuotient x y).snd) := by
  have hn : (goldenNorm y : ℚ) ≠ 0 := by
    exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
  have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd - y.snd ^ 2 ≠ 0 := by
    simpa [goldenNorm] using hn
  let A : ℚ := (goldenQuotientCoords x y).1
  let B : ℚ := (goldenQuotientCoords x y).2
  let m : ℤ := (goldenQuotient x y).fst
  let n : ℤ := (goldenQuotient x y).snd
  have hx1 : (x.fst : ℚ) = y.fst * A + y.snd * B := by
    dsimp [A, B, goldenQuotientCoords]
    rw [goldenQuotientNumerator_fst, goldenQuotientNumerator_snd]
    field_simp [hn']
    simp [goldenNorm]
    ring
  have hx2 : (x.snd : ℚ) =
      y.snd * A + y.fst * B + y.snd * B := by
    dsimp [A, B, goldenQuotientCoords]
    rw [goldenQuotientNumerator_fst, goldenQuotientNumerator_snd]
    field_simp [hn']
    simp [goldenNorm]
    ring
  have hr1 : ((goldenRemainder x y).fst : ℚ) =
      y.fst * (A - m) + y.snd * (B - n) := by
    simp only [goldenRemainder, goldenMul, golden_fst_sub, Int.cast_sub, Int.cast_add, Int.cast_mul,
      m, n]
    rw [hx1]
    ring
  have hr2 : ((goldenRemainder x y).snd : ℚ) =
      y.snd * (A - m) + y.fst * (B - n) + y.snd * (B - n) := by
    simp only [goldenRemainder, goldenMul, golden_snd_sub, Int.cast_sub, Int.cast_add, Int.cast_mul,
      m, n]
    rw [hx2]
    ring
  dsimp only [goldenNorm, goldenRatNorm]
  push_cast
  change _ = _ *
    ((A - (m : ℚ)) ^ 2 + (A - (m : ℚ)) * (B - (n : ℚ)) -
      (B - (n : ℚ)) ^ 2)
  rw [hr1, hr2]
  ring

/-- The concrete nearest-lattice remainder has strictly smaller norm size. -/
theorem golden_remainder_size_lt (x : GoldenInt) {y : GoldenInt} (hy : y ≠ 0) :
    goldenEuclideanSize (goldenRemainder x y) < goldenEuclideanSize y := by
  let A := (goldenQuotientCoords x y).1
  let B := (goldenQuotientCoords x y).2
  have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
  have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
  have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
    simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
  have hnpos : 0 < |(goldenNorm y : ℚ)| := abs_pos.mpr (by
    exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy)
  have hid := goldenRemainder_norm_rat_identity x y hy
  have hrat : |(goldenNorm (goldenRemainder x y) : ℚ)| <
      |(goldenNorm y : ℚ)| := by
    rw [hid, abs_mul]
    have := mul_lt_mul_of_pos_left hcell hnpos
    simpa [A, B, goldenQuotient] using this
  have hInt : |goldenNorm (goldenRemainder x y)| < |goldenNorm y| := by
    exact_mod_cast hrat
  change (goldenNorm (goldenRemainder x y)).natAbs <
    (goldenNorm y).natAbs
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hInt
  exact_mod_cast hInt

/-- Explicit quotient and remainder with strict natural absolute-norm decrease. -/
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)

/-- The golden integer ring is Euclidean for the absolute golden norm. -/
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
  r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
  r_wellFounded := (measure goldenEuclideanSize).wf
  remainder_lt := golden_remainder_size_lt
  mul_left_not_lt := by
    intro a b hb
    apply not_lt_of_ge
    rw [← golden_mul_eq, goldenEuclideanSize_mul]
    have hbSize : 1 ≤ goldenEuclideanSize b :=
      goldenEuclideanSize_pos_of_ne_zero hb
    exact Nat.le_mul_of_pos_right _ hbSize

end DkMath.FLT.Five
