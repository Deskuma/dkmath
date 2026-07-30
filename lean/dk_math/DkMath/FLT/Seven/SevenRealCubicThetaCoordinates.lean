/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicSourcePlane

#print "file: DkMath.FLT.Seven.SevenRealCubicThetaCoordinates"

namespace DkMath.FLT.Seven

namespace SevenRealCubicInt

/-- Constant coordinate after the integral change from `alpha` to
`theta = alpha - 3`. -/
def thetaConstInt (x : SevenRealCubicInt) : ℤ :=
  x.fst + 3 * x.snd + 9 * x.thd

/-- Linear theta coordinate after the integral change of basis. -/
def thetaLinearInt (x : SevenRealCubicInt) : ℤ :=
  x.snd + 6 * x.thd

/-- Quadratic theta coordinate after the integral change of basis. -/
def thetaSquareInt (x : SevenRealCubicInt) : ℤ :=
  x.thd

/-- Reconstruction from integral theta coordinates. -/
def ofThetaCoordinates (A B C : ℤ) : SevenRealCubicInt :=
  ofInt A +
    ofInt B * eisensteinAxis +
    ofInt C * eisensteinAxis ^ 2

@[simp] theorem eisensteinAxis_fst : eisensteinAxis.fst = -3 := rfl
@[simp] theorem eisensteinAxis_snd : eisensteinAxis.snd = 1 := rfl
@[simp] theorem eisensteinAxis_thd : eisensteinAxis.thd = 0 := rfl

theorem eisensteinAxis_sq_coordinates :
    eisensteinAxis ^ 2 = ⟨9, -6, 1⟩ := by
  ext <;> norm_num [eisensteinAxis, pow_two]

theorem ofThetaCoordinates_coordinates (A B C : ℤ) :
    thetaConstInt (ofThetaCoordinates A B C) = A ∧
      thetaLinearInt (ofThetaCoordinates A B C) = B ∧
      thetaSquareInt (ofThetaCoordinates A B C) = C := by
  norm_num [thetaConstInt, thetaLinearInt, thetaSquareInt,
    ofThetaCoordinates, eisensteinAxis_sq_coordinates]
  constructor
  · ring
  · ring

theorem theta_coordinate_decomposition (x : SevenRealCubicInt) :
    x =
      ofThetaCoordinates
        (thetaConstInt x) (thetaLinearInt x) (thetaSquareInt x) := by
  rcases x with ⟨a, b, c⟩
  ext <;>
    norm_num [thetaConstInt, thetaLinearInt, thetaSquareInt,
      ofThetaCoordinates,
      eisensteinAxis_sq_coordinates] <;> ring

theorem thetaSquareInt_eq_thd (x : SevenRealCubicInt) :
    thetaSquareInt x = x.thd :=
  rfl

theorem isSourcePlane_iff_thetaSquareInt_eq_zero
    (x : SevenRealCubicInt) :
    IsSourcePlane x ↔ thetaSquareInt x = 0 :=
  Iff.rfl

theorem leftSource_thetaCoordinates (a n : ℤ) :
    thetaConstInt (leftSource a n) = a - 3 * n ∧
      thetaLinearInt (leftSource a n) = -n ∧
      thetaSquareInt (leftSource a n) = 0 := by
  simp [thetaConstInt, thetaLinearInt, thetaSquareInt, leftSource]
  ring

theorem rightSource_thetaCoordinates (a n : ℤ) :
    thetaConstInt (rightSource a n) = a + 4 * n ∧
      thetaLinearInt (rightSource a n) = n ∧
      thetaSquareInt (rightSource a n) = 0 := by
  simp [thetaConstInt, thetaLinearInt, thetaSquareInt, rightSource]
  ring

#print axioms theta_coordinate_decomposition

end SevenRealCubicInt

end DkMath.FLT.Seven
