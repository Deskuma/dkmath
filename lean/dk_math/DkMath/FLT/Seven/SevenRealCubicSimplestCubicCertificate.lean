/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicSourcePlaneNormSeven
import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerDepth

#print "file: DkMath.FLT.Seven.SevenRealCubicSimplestCubicCertificate"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace SevenRealCubic

def sourcePlaneNormSevenForm (a b : ℤ) : ℤ :=
  a ^ 3 + 2 * a ^ 2 * b - a * b ^ 2 - b ^ 3

theorem sourcePlaneNormSevenForm_eq_norm (a b : ℤ) :
    sourcePlaneNormSevenForm a b = norm (linearSource a b) := by
  rw [norm_linearSource]
  rfl

def sourcePlaneNormSevenDiscriminant : ℤ :=
  2 ^ 2 * (-1) ^ 2 - 4 * 1 * (-1) ^ 3 -
    4 * 2 ^ 3 * (-1) - 27 * 1 ^ 2 * (-1) ^ 2 +
    18 * 1 * 2 * (-1) * (-1)

theorem sourcePlaneNormSevenDiscriminant_eq :
    sourcePlaneNormSevenDiscriminant = 49 := by
  norm_num [sourcePlaneNormSevenDiscriminant]

def sourcePlaneNormSevenQuadratic (a b : ℤ) : ℤ :=
  a ^ 2 + a * b + b ^ 2

def sourcePlaneNormSevenJacobian (a b : ℤ) : ℤ :=
  a ^ 3 - 12 * a ^ 2 * b - 15 * a * b ^ 2 - b ^ 3

def sourcePlaneNormSevenHessian (a b : ℤ) : ℤ :=
  (2 ^ 2 - 3 * 1 * (-1)) * a ^ 2 +
    (2 * (-1) - 9 * 1 * (-1)) * a * b +
    ((-1) ^ 2 - 3 * 2 * (-1)) * b ^ 2

theorem sourcePlaneNormSevenForm_covariant_identity (a b : ℤ) :
    sourcePlaneNormSevenJacobian a b ^ 2 =
      28 * sourcePlaneNormSevenQuadratic a b ^ 3 -
        27 * sourcePlaneNormSevenForm a b ^ 2 := by
  simp [sourcePlaneNormSevenJacobian, sourcePlaneNormSevenQuadratic,
    sourcePlaneNormSevenForm]
  ring

theorem sourcePlaneNormSevenHessian_eq (a b : ℤ) :
    sourcePlaneNormSevenHessian a b =
      7 * sourcePlaneNormSevenQuadratic a b := by
  simp [sourcePlaneNormSevenHessian, sourcePlaneNormSevenQuadratic]
  ring

theorem sourcePlaneNormSevenForm_factor (a b : ℤ) :
    sourcePlaneNormSevenForm a b =
      (a + 3 * b) ^ 3 - 7 * b * (a + 2 * b) ^ 2 := by
  simp [sourcePlaneNormSevenForm]
  ring

def sourcePlaneNormSevenReducedForm (b c : ℤ) : ℤ :=
  b ^ 3 - 14 * b ^ 2 * c + 49 * b * c ^ 2 - 49 * c ^ 3

theorem sourcePlaneNormSevenForm_substitution (b c : ℤ) :
    sourcePlaneNormSevenForm (7 * c - 3 * b) b =
      -7 * sourcePlaneNormSevenReducedForm b c := by
  simp [sourcePlaneNormSevenForm, sourcePlaneNormSevenReducedForm]
  ring

theorem exists_sourcePlaneNormSeven_reduction
    {a b : ℤ} (hF : sourcePlaneNormSevenForm a b = -7) :
    ∃ c : ℤ,
      a = 7 * c - 3 * b ∧
        sourcePlaneNormSevenReducedForm b c = 1 := by
  have hcube : (7 : ℤ) ∣ (a + 3 * b) ^ 3 := by
    refine ⟨b * (a + 2 * b) ^ 2 - 1, ?_⟩
    have hfactor := sourcePlaneNormSevenForm_factor a b
    rw [hfactor] at hF
    nlinarith
  have hbase : (7 : ℤ) ∣ a + 3 * b := by
    exact (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hcube
  rcases hbase with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · linarith
  · have hsub : sourcePlaneNormSevenForm (7 * c - 3 * b) b = -7 := by
      rw [show 7 * c - 3 * b = a by linarith]
      exact hF
    rw [sourcePlaneNormSevenForm_substitution] at hsub
    nlinarith

theorem sourcePlaneNormSevenQuadratic_substitution (b c : ℤ) :
    sourcePlaneNormSevenQuadratic (7 * c - 3 * b) b =
      7 * (b ^ 2 - 5 * b * c + 7 * c ^ 2) := by
  simp [sourcePlaneNormSevenQuadratic]
  ring

theorem sourcePlaneNormSevenEisensteinShadow (b c : ℤ) :
    b ^ 2 - 5 * b * c + 7 * c ^ 2 =
      (b - 2 * c) ^ 2 - (b - 2 * c) * c + c ^ 2 := by
  ring

theorem sourcePlaneNormSevenQuadratic_dvd_of_norm_eq_neg_seven
    {a b : ℤ} (hF : sourcePlaneNormSevenForm a b = -7) :
    (7 : ℤ) ∣ sourcePlaneNormSevenQuadratic a b := by
  obtain ⟨c, hc, _⟩ := exists_sourcePlaneNormSeven_reduction hF
  rw [hc, sourcePlaneNormSevenQuadratic_substitution]
  exact dvd_mul_right 7 _

theorem sourcePlaneNormSevenJacobian_dvd_of_norm_eq_neg_seven
    {a b : ℤ} (hF : sourcePlaneNormSevenForm a b = -7) :
    (7 : ℤ) ∣ sourcePlaneNormSevenJacobian a b := by
  obtain ⟨c, hc, _⟩ := exists_sourcePlaneNormSeven_reduction hF
  have hmod : (a : ZMod 7) = -3 * (b : ZMod 7) := by
    have hz : ((a + 3 * b : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr (by
        rw [hc]
        convert dvd_mul_right 7 c using 1
        · ring)
    push_cast at hz
    linear_combination hz
  have hz : (sourcePlaneNormSevenJacobian a b : ZMod 7) = 0 := by
    rw [sourcePlaneNormSevenJacobian]
    push_cast
    rw [hmod]
    ring_nf
    rw [show (91 : ZMod 7) = 0 by decide, mul_zero]
    simp
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz

theorem sourcePlaneNormSevenCovariant_certificate
    {a b : ℤ} (hF : sourcePlaneNormSevenForm a b = -7) :
    ∃ q k : ℤ,
      sourcePlaneNormSevenQuadratic a b = 7 * q ∧
      sourcePlaneNormSevenJacobian a b = 7 * k ∧
      k ^ 2 + 27 = 196 * q ^ 3 := by
  obtain ⟨q, hq⟩ := sourcePlaneNormSevenQuadratic_dvd_of_norm_eq_neg_seven hF
  obtain ⟨k, hk⟩ := sourcePlaneNormSevenJacobian_dvd_of_norm_eq_neg_seven hF
  refine ⟨q, k, hq, hk, ?_⟩
  have hcov := sourcePlaneNormSevenForm_covariant_identity a b
  rw [hF, hq, hk] at hcov
  nlinarith

set_option maxHeartbeats 2000000 in
-- The forward divisibility induction normalizes both theta quotients.
theorem thetaNilpotentDepth_succ_pow_seven
    (x : SevenRealCubicInt) (n : ℕ)
    (hdepth : ThetaNilpotentDepth n x) :
    ThetaNilpotentDepth (n + 1) (x ^ 7) := by
  let A : ℤ := thetaConstInt x
  let B : ℤ := thetaLinearInt x
  let C : ℤ := thetaSquareInt x
  have hx : x = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition x
  have hlin : thetaLinearInt (x ^ 7) =
      7 * seventhThetaLinearQuotient A B C := by
    rw [hx]
    exact thetaLinear_pow_seven A B C
  have hsq : thetaSquareInt (x ^ 7) =
      7 * seventhThetaSquareQuotient A B C := by
    rw [hx]
    exact thetaSquare_pow_seven A B C
  let GB := seventhThetaLinearBFactor A B C
  let GC := seventhThetaLinearCFactor A C
  have hB : (7 : ℤ) ^ n ∣ B := by
    simpa [B] using hdepth.1
  have hC : (7 : ℤ) ^ n ∣ C := by
    simpa [C] using hdepth.2
  have hBterm : (7 : ℤ) ^ n ∣ B * GB :=
    dvd_mul_of_dvd_left hB GB
  have hC2 : (7 : ℤ) ^ n ∣ C ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hC C
  have hCterm : (7 : ℤ) ^ n ∣ 7 * C ^ 2 * GC := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (dvd_mul_of_dvd_left hC2 (7 * GC))
  have hquotlin : (7 : ℤ) ^ n ∣ seventhThetaLinearQuotient A B C := by
    change (7 : ℤ) ^ n ∣ B * GB + 7 * C ^ 2 * GC
    exact dvd_add hBterm hCterm
  let HB := seventhThetaSquareBFactor A B
  let HC := seventhThetaSquareCFactor A B C
  have hBsq : (7 : ℤ) ^ n ∣ B ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hB B
  have hBtermSq : (7 : ℤ) ^ n ∣ B ^ 2 * HB :=
    dvd_mul_of_dvd_left hBsq HB
  have hCtermSq : (7 : ℤ) ^ n ∣ C * HC :=
    dvd_mul_of_dvd_left hC HC
  have hquotsq : (7 : ℤ) ^ n ∣ seventhThetaSquareQuotient A B C := by
    change (7 : ℤ) ^ n ∣ C * HC + B ^ 2 * HB
    exact dvd_add hCtermSq hBtermSq
  constructor
  · rcases hquotlin with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hlin, hq, pow_succ]
    ring
  · rcases hquotsq with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hsq, hq, pow_succ]
    ring

theorem thetaNilpotentDepth_pow_seven_pow
    (u : SevenRealCubicIntˣ) (n : ℕ) :
    ThetaNilpotentDepth n
      (((u : SevenRealCubicInt) ^ (7 ^ n))) := by
  induction n with
  | zero =>
      simp [ThetaNilpotentDepth]
  | succ n ih =>
      have hnext := thetaNilpotentDepth_succ_pow_seven
        ((u : SevenRealCubicInt) ^ (7 ^ n)) n ih
      have hpow :
          ((u : SevenRealCubicInt) ^ (7 ^ n)) ^ 7 =
            (u : SevenRealCubicInt) ^ (7 ^ (n + 1)) := by
        rw [← pow_mul, Nat.pow_succ]
      rw [← hpow]
      exact hnext

theorem exists_theta_line_square_parameter
    {L S : ℤ} (hLS : 3 * L = 14 * S) :
    ∃ m : ℤ, L = 14 * m ∧ S = 3 * m := by
  have hdiv : (3 : ℤ) ∣ 14 * S := by
    refine ⟨L, ?_⟩
    linarith
  have hdiv' : (3 : ℤ) ∣ S * 14 := by
    simpa [mul_comm] using hdiv
  have hS : (3 : ℤ) ∣ S := by
    exact (show IsCoprime (3 : ℤ) 14 by norm_num).dvd_of_dvd_mul_right hdiv'
  rcases hS with ⟨m, hm⟩
  refine ⟨m, ?_, hm⟩
  nlinarith [hLS]

theorem sourcePlaneNormSevenAxis_mul_thetaCoordinates_parameter
    (A m : ℤ) :
    sourcePlaneNormSevenAxis * ofThetaCoordinates A (14 * m) (3 * m) =
      linearSource (2 * A - 21 * m) (-3 * A + 28 * m) := by
  ext
  all_goals
    norm_num [sourcePlaneNormSevenAxis, linearSource, ofThetaCoordinates,
      eisensteinAxis_sq_coordinates, eisensteinAxis, SevenRealCubicInt.mul,
      ofInt, pow_two]
  all_goals ring

theorem sourcePlaneNormSeven_inverse_coordinate_transform (A m : ℤ) :
    let a := 2 * A - 21 * m
    let b := -3 * A + 28 * m
    A = -4 * a - 3 * b ∧
      7 * m = -(3 * a + 2 * b) := by
  dsimp
  constructor <;> ring

theorem directOrbitTrivialCommonFactorSharpenedPacket_correction_depth_nine
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p}
    (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) :
    ThetaNilpotentDepth 9
      (((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)) := by
  have hdepth := thetaNilpotentDepth_pow_seven_pow P.t 9
  simpa only [Units.val_pow_eq_pow_val] using hdepth

theorem directOrbitTrivialCommonFactorSharpenedPacket_correction_coordinate_transform
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p}
    (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) :
    ∃ A m : ℤ,
      sourcePlaneNormSevenAxis *
          (((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)) =
        linearSource (2 * A - 21 * m) (-3 * A + 28 * m) ∧
      (7 : ℤ) ^ 9 ∣ m ∧
      (7 : ℤ) ^ 10 ∣
        3 * (2 * A - 21 * m) + 2 * (-3 * A + 28 * m) := by
  obtain ⟨hline, _, _, _⟩ :=
    directOrbitTrivialCommonFactorSharpenedPacket_correction_line P
  let Y : SevenRealCubicInt :=
    ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)
  let A : ℤ := thetaConstInt Y
  let L : ℤ := thetaLinearInt Y
  let S : ℤ := thetaSquareInt Y
  have hLS : 3 * L = 14 * S := by
    simpa [L, S, Y] using hline
  obtain ⟨m, hmL, hmS⟩ := exists_theta_line_square_parameter hLS
  have hdepth : ThetaNilpotentDepth 9 Y := by
    simpa [Y] using
      directOrbitTrivialCommonFactorSharpenedPacket_correction_depth_nine P
  have hSdiv : (7 : ℤ) ^ 9 ∣ S := by
    simpa [S] using hdepth.2
  have hprod : (7 : ℤ) ^ 9 ∣ m * 3 := by
    simpa [hmS, mul_comm] using hSdiv
  have hmd : (7 : ℤ) ^ 9 ∣ m := by
    exact (show IsCoprime ((7 : ℤ) ^ 9) 3 by norm_num).dvd_of_dvd_mul_right hprod
  have hY : Y = ofThetaCoordinates A L S := by
    exact theta_coordinate_decomposition Y
  have hxy : sourcePlaneNormSevenAxis * Y =
      linearSource (2 * A - 21 * m) (-3 * A + 28 * m) := by
    rw [hY, hmL, hmS]
    exact sourcePlaneNormSevenAxis_mul_thetaCoordinates_parameter A m
  refine ⟨A, m, hxy, hmd, ?_⟩
  rcases hmd with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  rw [show (10 : ℕ) = 9 + 1 by norm_num, pow_succ, hq]
  ring

end SevenRealCubic
end
end DkMath.FLT.Seven
