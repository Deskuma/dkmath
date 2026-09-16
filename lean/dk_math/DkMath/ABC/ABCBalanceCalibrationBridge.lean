/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNBalanceCalibration

#print "file: DkMath.ABC.ABCBalanceCalibrationBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Pointwise calibration and outer ABC balance

This bridge keeps the GN channel coordinates from checkpoint 000 stable while
exposing the pointwise correction obtained by substituting the actual residual
into the existing epsilon theorem.  It also places the signed outer ABC gap
in a support/depth mass coordinate system.

The GN balance is support minus depth.  The outer ABC balance is depth minus
support, matching the pre-existing `abcGap` orientation; the two coordinates
are intentionally not identified here.
-/

namespace DkMath.ABC

/-- Pointwise epsilon correction supplied by one triple's GN residual. -/
noncomputable def GNPointwiseCalibrationCorrection
    (T : Triple) (p : ℕ) (ρ : ℝ) : ℝ :=
  (GNCalibrationResidual T p ρ + Real.log (rad p : ℝ)) /
    (((p - 1 : ℕ) : ℝ) * T.radLog)

/-- Input radical support mass in the outer ABC balance. -/
noncomputable def ABCInputSupportMass (T : Triple) : ℝ :=
  Real.log (rad (T.a * T.b) : ℝ)

/-- Output valuation-depth mass in the outer ABC balance. -/
noncomputable def ABCOutputDepthMass (T : Triple) : ℝ :=
  valuationExcess T.c

/-- Total outer ABC support/depth mass. -/
noncomputable def ABCOuterMass (T : Triple) : ℝ :=
  ABCInputSupportMass T + ABCOutputDepthMass T

/-- Signed outer ABC balance, oriented as the existing `abcGap`. -/
noncomputable def ABCOuterBalance (T : Triple) : ℝ :=
  ABCOutputDepthMass T - ABCInputSupportMass T

/-- The pointwise residual directly controls the intrinsic epsilon correction. -/
theorem Triple.abcEpsilon_le_GNEpsilon_add_pointwiseCalibrationCorrection
    (T : Triple) {p : ℕ} {ρ : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcEpsilon ≤
      GNEpsilon p ρ + GNPointwiseCalibrationCorrection T p ρ := by
  have h :=
    T.abcEpsilon_le_GNEpsilon_add_correction_of_calibrationResidual_le
      hp hpOdd ha hb (ρ := ρ) (C := GNCalibrationResidual T p ρ) le_rfl
  simpa [GNPointwiseCalibrationCorrection] using h

/-- A uniform residual allowance is an upper envelope for pointwise correction. -/
theorem GNPointwiseCalibrationCorrection_le_of_calibrationResidual_le
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hcal : GNCalibrationResidual T p ρ ≤ C) :
    GNPointwiseCalibrationCorrection T p ρ ≤
      (C + Real.log (rad p : ℝ)) /
        (((p - 1 : ℕ) : ℝ) * T.radLog) := by
  have hpred : 0 < (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hrad : 0 < T.radLog := by
    simpa [Triple.radLog] using T.log_rad_abc_pos ha hb
  have hden : 0 < (((p - 1 : ℕ) : ℝ) * T.radLog) :=
    mul_pos hpred hrad
  unfold GNPointwiseCalibrationCorrection
  apply (div_le_div_iff_of_pos_right hden).2
  linarith

/-- The outer output depth mass is reconstructed from outer mass and balance. -/
theorem ABCOutputDepthMass_eq_half_outerMass_add_balance
    (T : Triple) :
    ABCOutputDepthMass T =
      (ABCOuterMass T + ABCOuterBalance T) / 2 := by
  unfold ABCOuterMass ABCOuterBalance
  ring

/-- The outer input support mass is reconstructed from outer mass and balance. -/
theorem ABCInputSupportMass_eq_half_outerMass_sub_balance
    (T : Triple) :
    ABCInputSupportMass T =
      (ABCOuterMass T - ABCOuterBalance T) / 2 := by
  unfold ABCOuterMass ABCOuterBalance
  ring

/-- The outer balance is exactly the existing signed ABC gap. -/
theorem Triple.ABCOuterBalance_eq_abcGap
    (T : Triple) (ha : 0 < T.a) (hb : 0 < T.b) :
    ABCOuterBalance T = T.abcGap := by
  simpa [ABCOuterBalance, ABCOutputDepthMass, ABCInputSupportMass] using
    (T.abcGap_eq_valuationExcess_sub_log_rad_ab ha hb).symm

/-- The outer balance is the intrinsic ABC epsilon times its radical scale. -/
theorem Triple.ABCOuterBalance_eq_abcEpsilon_mul_radLog
    (T : Triple) (ha : 0 < T.a) (hb : 0 < T.b) :
    ABCOuterBalance T = T.abcEpsilon * T.radLog := by
  calc
    ABCOuterBalance T = T.abcGap := T.ABCOuterBalance_eq_abcGap ha hb
    _ = T.abcEpsilon * T.radLog := T.abcGap_eq_abcEpsilon_mul_radLog ha hb

/-- The zero outer-balance contour is exactly the zero ABC-gap contour. -/
theorem ABCOuterBalance_eq_zero_iff_abcGap_eq_zero
    (T : Triple) (ha : 0 < T.a) (hb : 0 < T.b) :
    ABCOuterBalance T = 0 ↔ T.abcGap = 0 := by
  rw [T.ABCOuterBalance_eq_abcGap ha hb]

end DkMath.ABC
