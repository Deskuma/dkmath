/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSharpenedBranch
import DkMath.FLT.Seven.SevenRealCubicThetaCoordinates
import DkMath.FLT.Seven.SevenRealCubicCoprimeExtraction

#print "file: DkMath.FLT.Seven.SevenRealCubicSourcePlaneNormSeven"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace SevenRealCubic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem inv_two_zmod_seven_source_plane : (2 : ZMod 7)⁻¹ = 4 := by
  exact ZMod.inv_eq_of_mul_eq_one 7 2 4 (by
    change ((8 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [ZMod.natCast_eq_natCast_iff]
    decide)

private theorem inv_nine_zmod_seven_source_plane : (9 : ZMod 7)⁻¹ = 4 := by
  exact ZMod.inv_eq_of_mul_eq_one 7 9 4 (by
    change ((36 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [ZMod.natCast_eq_natCast_iff]
    decide)

private theorem inv_ten_zmod_seven_source_plane : (10 : ZMod 7)⁻¹ = 5 := by
  exact ZMod.inv_eq_of_mul_eq_one 7 10 5 (by
    change ((50 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [ZMod.natCast_eq_natCast_iff]
    decide)

def sourcePlaneNormSevenAxis : SevenRealCubicInt :=
  linearSource 2 (-3)

theorem sourcePlaneNormSevenAxis_eq_two_sub_three_alpha :
    sourcePlaneNormSevenAxis =
      (2 : SevenRealCubicInt) - 3 * alpha := by
  rw [sourcePlaneNormSevenAxis, linearSource_eq]
  rfl

theorem sourcePlaneNormSevenAxis_norm :
    norm sourcePlaneNormSevenAxis = -7 := by
  norm_num [sourcePlaneNormSevenAxis, linearSource, SevenRealCubicInt.norm]

theorem sourcePlaneNormSevenAxis_isSourcePlane :
    IsSourcePlane sourcePlaneNormSevenAxis := by
  simp [sourcePlaneNormSevenAxis, linearSource, IsSourcePlane]

theorem sourcePlaneNormSevenAxis_thetaSquare_mul
    (A B C : ℤ) :
    thetaSquareInt
        (sourcePlaneNormSevenAxis * ofThetaCoordinates A B C) =
      -3 * B + 14 * C := by
  norm_num [sourcePlaneNormSevenAxis, linearSource, thetaSquareInt,
    ofThetaCoordinates, eisensteinAxis_sq_coordinates, eisensteinAxis,
    SevenRealCubicInt.mul, ofInt, pow_two]
  ring

theorem sourcePlaneNormSevenAxis_isSourcePlane_mul_of_theta_relation
    (A B C : ℤ) (hBC : 3 * B = 14 * C) :
    IsSourcePlane
      (sourcePlaneNormSevenAxis * ofThetaCoordinates A B C) := by
  rw [isSourcePlane_iff_thetaSquareInt_eq_zero,
    sourcePlaneNormSevenAxis_thetaSquare_mul]
  linarith

theorem sourcePlaneNormSevenAxis_thetaSquare_mul_of
    (x : SevenRealCubicInt) :
    thetaSquareInt (sourcePlaneNormSevenAxis * x) =
      -3 * thetaLinearInt x + 14 * thetaSquareInt x := by
  rw [theta_coordinate_decomposition x]
  have hcoords := ofThetaCoordinates_coordinates
    (thetaConstInt x) (thetaLinearInt x) (thetaSquareInt x)
  rw [hcoords.2.1, hcoords.2.2]
  exact sourcePlaneNormSevenAxis_thetaSquare_mul
    (thetaConstInt x) (thetaLinearInt x) (thetaSquareInt x)

theorem norm_linearSource :
    ∀ a b : ℤ,
      norm (linearSource a b) =
        a ^ 3 + 2 * a ^ 2 * b - a * b ^ 2 - b ^ 3
  | a, b => by
      norm_num [linearSource, SevenRealCubicInt.norm]

theorem sourcePlaneNormSevenAxis_eq_linearSource :
    sourcePlaneNormSevenAxis = linearSource 2 (-3) := rfl

theorem sourcePlaneNormSevenAxis_mul_eq_self :
    sourcePlaneNormSevenAxis * (1 : SevenRealCubicInt) =
      linearSource 2 (-3) := by
  simp [sourcePlaneNormSevenAxis]

def sourcePlaneNormSevenY1 : SevenRealCubicInt :=
  ofThetaCoordinates 9 14 3

def sourcePlaneNormSevenY2 : SevenRealCubicInt :=
  ofThetaCoordinates (-10) (-14) (-3)

theorem sourcePlaneNormSevenY1_norm :
    norm sourcePlaneNormSevenY1 = 1 := by
  norm_num [sourcePlaneNormSevenY1, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates, eisensteinAxis, SevenRealCubicInt.norm,
    SevenRealCubicInt.mul, ofInt, pow_two]

theorem sourcePlaneNormSevenY2_norm :
    norm sourcePlaneNormSevenY2 = 1 := by
  norm_num [sourcePlaneNormSevenY2, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates, eisensteinAxis, SevenRealCubicInt.norm,
    SevenRealCubicInt.mul, ofInt, pow_two]

private theorem sourcePlaneNormSeven_isUnit_of_norm_one
    {x : SevenRealCubicInt} (hx : norm x = 1) : IsUnit x := by
  apply IsUnit.of_mul_eq_one
    (rotateEquiv x * rotateEquiv (rotateEquiv x))
  calc
    x * (rotateEquiv x * rotateEquiv (rotateEquiv x)) =
        x * rotateEquiv x * rotateEquiv (rotateEquiv x) := by ring
    _ = (norm x : SevenRealCubicInt) :=
      mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm x
    _ = 1 := by norm_num [hx]

theorem sourcePlaneNormSevenY1_isUnit :
    IsUnit sourcePlaneNormSevenY1 :=
  sourcePlaneNormSeven_isUnit_of_norm_one sourcePlaneNormSevenY1_norm

theorem sourcePlaneNormSevenY2_isUnit :
    IsUnit sourcePlaneNormSevenY2 :=
  sourcePlaneNormSeven_isUnit_of_norm_one sourcePlaneNormSevenY2_norm

noncomputable def sourcePlaneNormSevenY1Unit : SevenRealCubicIntˣ :=
  sourcePlaneNormSevenY1_isUnit.unit

noncomputable def sourcePlaneNormSevenY2Unit : SevenRealCubicIntˣ :=
  sourcePlaneNormSevenY2_isUnit.unit

@[simp] theorem sourcePlaneNormSevenY1Unit_val :
    (sourcePlaneNormSevenY1Unit : SevenRealCubicInt) =
      sourcePlaneNormSevenY1 :=
  sourcePlaneNormSevenY1_isUnit.unit_spec

@[simp] theorem sourcePlaneNormSevenY2Unit_val :
    (sourcePlaneNormSevenY2Unit : SevenRealCubicInt) =
      sourcePlaneNormSevenY2 :=
  sourcePlaneNormSevenY2_isUnit.unit_spec

theorem linearSource_neg_three_one_eq_eisensteinAxis :
    linearSource (-3) 1 = eisensteinAxis := by
  ext <;> norm_num [linearSource, eisensteinAxis]

theorem linearSource_one_two_eq_ramifiedAxis :
    linearSource 1 2 = ramifiedAxis := by
  ext <;> norm_num [linearSource, ramifiedAxis]

theorem linearSource_two_neg_three_eq_sourcePlaneNormSevenAxis :
    linearSource 2 (-3) = sourcePlaneNormSevenAxis := by
  rfl

theorem norm_linearSource_neg_three_one :
    norm (linearSource (-3) 1) = -7 := by
  rw [norm_linearSource]
  norm_num

theorem norm_linearSource_one_two :
    norm (linearSource 1 2) = -7 := by
  rw [norm_linearSource]
  norm_num

theorem norm_linearSource_two_neg_three :
    norm (linearSource 2 (-3)) = -7 := by
  rw [norm_linearSource]
  norm_num

theorem sourcePlaneNormSevenAxis_mul_Y0_eq :
    sourcePlaneNormSevenAxis * (1 : SevenRealCubicInt) =
      linearSource 2 (-3) := by
  simp [sourcePlaneNormSevenAxis]

theorem sourcePlaneNormSevenAxis_mul_Y1_eq_eisensteinAxis :
    sourcePlaneNormSevenAxis * sourcePlaneNormSevenY1 =
      eisensteinAxis := by
  ext <;>
    norm_num [sourcePlaneNormSevenAxis, sourcePlaneNormSevenY1,
      linearSource, ofThetaCoordinates, eisensteinAxis_sq_coordinates,
      eisensteinAxis, SevenRealCubicInt.mul, ofInt, pow_two]

theorem sourcePlaneNormSevenAxis_mul_Y2_eq_ramifiedAxis :
    sourcePlaneNormSevenAxis * sourcePlaneNormSevenY2 =
      ramifiedAxis := by
  ext <;>
    norm_num [sourcePlaneNormSevenAxis, sourcePlaneNormSevenY2,
      linearSource, ofThetaCoordinates, eisensteinAxis_sq_coordinates,
      eisensteinAxis, ramifiedAxis, SevenRealCubicInt.mul, ofInt, pow_two]

theorem sourcePlaneNormSevenY1_projectiveLog :
    projectiveLog (Additive.ofMul sourcePlaneNormSevenY1Unit) = (0, 5) := by
  ext <;>
    norm_num [projectiveLog_apply, unitNilpotentX, unitNilpotentY,
    sourcePlaneNormSevenY1Unit_val, sourcePlaneNormSevenY1,
    ofThetaCoordinates, eisensteinAxis_sq_coordinates, eisensteinAxis,
    thetaConstModSeven, thetaLinearModSeven, thetaSquareModSeven,
    inv_two_zmod_seven_source_plane,
    inv_nine_zmod_seven_source_plane, div_eq_mul_inv,
    SevenRealCubicInt.mul, ofInt, pow_two] <;> decide

theorem sourcePlaneNormSevenY2_projectiveLog :
    projectiveLog (Additive.ofMul sourcePlaneNormSevenY2Unit) = (0, 1) := by
  ext <;>
    norm_num [projectiveLog_apply, unitNilpotentX, unitNilpotentY,
    sourcePlaneNormSevenY2Unit_val, sourcePlaneNormSevenY2,
    ofThetaCoordinates, eisensteinAxis_sq_coordinates, eisensteinAxis,
    thetaConstModSeven, thetaLinearModSeven, thetaSquareModSeven,
    inv_two_zmod_seven_source_plane,
    inv_ten_zmod_seven_source_plane, div_eq_mul_inv,
    SevenRealCubicInt.mul, ofInt, pow_two] <;> decide

theorem sourcePlaneNormSevenY0_projectiveLog :
    projectiveLog (Additive.ofMul (1 : SevenRealCubicIntˣ)) = (0, 0) := by
  rw [projectiveLog_apply]
  simp

theorem directOrbitTrivialCommonFactorSharpenedPacket_correction_line
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p}
    (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) :
    3 * thetaLinearInt
          ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt) =
        14 * thetaSquareInt
          ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt) ∧
      (P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) ≠ 1 ∧
      norm ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 ∧
      projectiveLog
          (Additive.ofMul (P.t ^ (7 ^ 9) : SevenRealCubicIntˣ)) = 0 := by
  let Y : SevenRealCubicIntˣ := P.t ^ (7 ^ 9)
  have htrace := directOrbitDeepJet_trace_plane_form
    (directOrbitDeepJetWUnit h.squareRefinement P.eta : SevenRealCubicInt)
    (directOrbitDeepJet_normalized_trace_zero h P.c_eq_one P.eta
      P.gap_scalar_eq)
  have hW := congrArg
    (fun u : SevenRealCubicIntˣ => (u : SevenRealCubicInt)) P.correction_eq
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at hW
  rw [hW] at htrace
  have htraceY :
      directOrbitTracePlaneForm
          ((directOrbitDeepJetRho : SevenRealCubicInt) * (Y : SevenRealCubicInt)) =
        0 := by
    simpa [Y] using htrace
  rw [directOrbitTracePlaneForm_rho_mul] at htraceY
  have hline :
      3 * thetaLinearInt (Y : SevenRealCubicInt) =
        14 * thetaSquareInt (Y : SevenRealCubicInt) := by
    linarith
  have hnormY : norm (Y : SevenRealCubicInt) = 1 := by
    have ht : norm ((P.t : SevenRealCubicInt) ^ (7 ^ 9)) = 1 := by
      rw [SevenRealCubicInt.norm_pow, P.correction_norm_eq_one]
      norm_num
    simpa [Y, Units.val_pow_eq_pow_val] using ht
  have hlogY : projectiveLog (Additive.ofMul Y) = 0 := by
    apply (unit_isSeventhPower_iff_projectiveLog_eq_zero Y).mp
    refine ⟨P.t ^ (7 ^ 8), ?_⟩
    dsimp [Y]
    rw [← pow_mul]
  exact ⟨by simpa [Y] using hline, P.correction_ne_one,
    by simpa [Y] using hnormY, by simpa [Y] using hlogY⟩

theorem directOrbitTrivialCommonFactorSharpenedPacket_source_plane_landing
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p}
    (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) :
    IsSourcePlane
        (sourcePlaneNormSevenAxis *
          ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)) ∧
      norm
          (sourcePlaneNormSevenAxis *
            ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)) = -7 := by
  obtain ⟨hline, _, hnormY, _⟩ :=
    directOrbitTrivialCommonFactorSharpenedPacket_correction_line P
  have htheta := sourcePlaneNormSevenAxis_thetaSquare_mul_of
    ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)
  have hzero : thetaSquareInt
      (sourcePlaneNormSevenAxis *
        ((P.t ^ (7 ^ 9) : SevenRealCubicIntˣ) : SevenRealCubicInt)) = 0 := by
    rw [htheta]
    linarith
  refine ⟨(isSourcePlane_iff_thetaSquareInt_eq_zero _).mpr hzero, ?_⟩
  rw [SevenRealCubicInt.norm_mul, sourcePlaneNormSevenAxis_norm, hnormY]
  norm_num

end SevenRealCubic
end
end DkMath.FLT.Seven
