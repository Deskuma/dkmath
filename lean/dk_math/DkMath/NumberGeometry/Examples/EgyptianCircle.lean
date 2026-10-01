/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Radical
import DkMath.SilverRatio.Sqrt2Lemmas

namespace DkMath.NumberGeometry.Examples.EgyptianCircle

open scoped InnerProductSpace
noncomputable section

open DkMath.NumberGeometry
open DkMath.SilverRatio.Sqrt2

/-!
# Exact Egyptian-circle calibrations

This module records only explicit square-mass identities for named points.
It does not formalize a historical construction or any unproved incidence
from the motivating GeoGebra draft.
-/

/-- The first coordinate unit direction. -/
def xDirection : Point := EuclideanSpace.single 0 1

/-- The second coordinate unit direction. -/
def yDirection : Point := EuclideanSpace.single 1 1

/-- The origin used as the center of the calibration levels. -/
def origin : Point := 0

/-- The exact mass-three radical point corresponding to `(1, sqrt 2)`. -/
def egyptianW : Point :=
  origin + xDirection + sqrt2 • yDirection

/-- The exact point at radius three on the first coordinate axis. -/
def radiusThreePoint : Point := 3 • xDirection

/-- The exact Keystone N coordinate from the bounded source formula. -/
def keyN : Point :=
  (2 - sqrt2 / 2) • xDirection + (2 + sqrt2 / 2) • yDirection

/-- The two coordinate directions are orthogonal. -/
theorem inner_xDirection_yDirection :
    ⟪xDirection, yDirection⟫_ℝ = 0 := by
  change ⟪EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)⟫_ℝ = 0
  rw [EuclideanSpace.inner_single_left]
  simp

/-- The radical point `W` has square mass three from the origin. -/
theorem pairMass_origin_egyptianW :
    pairMass origin egyptianW = 3 := by
  have hrad := pairMass_radical_of_inner_eq_zero
    origin xDirection yDirection (m := (2 : ℝ)) (by norm_num)
    inner_xDirection_yDirection
  calc
    pairMass origin egyptianW =
        ‖xDirection‖ ^ 2 + (2 : ℝ) * ‖yDirection‖ ^ 2 := by
      simpa [egyptianW, origin, sqrt2] using hrad
    _ = 3 := by simp [xDirection, yDirection]; norm_num

/-- The radius-three calibration point has square mass nine. -/
theorem pairMass_origin_radiusThreePoint :
    pairMass origin radiusThreePoint = 9 := by
  rw [pairMass, pairVec, origin, radiusThreePoint]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [xDirection]
  norm_num

/-- The explicit Keystone N coordinate has square mass nine. -/
theorem pairMass_origin_keyN :
    pairMass origin keyN = 9 := by
  rw [pairMass, pairVec, origin, keyN]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [xDirection, yDirection, sub_zero, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, Fin.sum_univ_two,
    Fin.isValue]
  norm_num
  calc
    (2 - sqrt2 / 2) ^ 2 + (2 + sqrt2 / 2) ^ 2 =
        8 + sqrt2 ^ 2 / 2 := by ring
    _ = 9 := by rw [sqrt2_sq]; norm_num

/-- The mass-three point lies on the origin-centered level three. -/
theorem egyptianW_mem_massLevelSet :
    egyptianW ∈ MassLevelSet origin 3 := by
  rw [mem_massLevelSet]
  exact pairMass_origin_egyptianW

/-- The radius-three point lies on the origin-centered level nine. -/
theorem radiusThreePoint_mem_massLevelSet :
    radiusThreePoint ∈ MassLevelSet origin 9 := by
  rw [mem_massLevelSet]
  exact pairMass_origin_radiusThreePoint

end
end DkMath.NumberGeometry.Examples.EgyptianCircle
