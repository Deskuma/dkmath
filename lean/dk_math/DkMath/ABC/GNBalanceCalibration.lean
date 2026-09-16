/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABCEpsilonSlopeBridge

#print "file: DkMath.ABC.GNBalanceCalibration"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# ABC/GN balance and calibration coordinates

This module makes the two existing non-exceptional GN channel components
explicit.  The definitions are coordinate aliases: they do not introduce a
new support product, valuation quantity, or arithmetic estimate.

The signed calibration residual is the pointwise form of the existing affine
channel budget.  No uniform bound on that residual is asserted here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- Fresh non-exceptional GN support log mass. -/
noncomputable def GNChannelSupportMass (T : Triple) (p : ℕ) : ℝ :=
  Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ)

/-- Non-exceptional GN valuation-depth mass. -/
noncomputable def GNChannelDepthMass (T : Triple) (p : ℕ) : ℝ :=
  GNNonExceptionalValuationExcess p T.a T.b

/-- Total non-exceptional GN channel mass. -/
noncomputable def GNChannelMass (T : Triple) (p : ℕ) : ℝ :=
  GNChannelSupportMass T p + GNChannelDepthMass T p

/-- Signed support-minus-depth balance coordinate. -/
noncomputable def GNChannelBalance (T : Triple) (p : ℕ) : ℝ :=
  GNChannelSupportMass T p - GNChannelDepthMass T p

/-- Pointwise signed residual of the channel mass at slope `ρ`. -/
noncomputable def GNCalibrationResidual
    (T : Triple) (p : ℕ) (ρ : ℝ) : ℝ :=
  GNChannelMass T p - ρ * T.radLog

/-- The support mass is reconstructed from total mass and balance. -/
theorem GNChannelSupportMass_eq_half_mass_add_balance
    (T : Triple) (p : ℕ) :
    GNChannelSupportMass T p =
      (GNChannelMass T p + GNChannelBalance T p) / 2 := by
  unfold GNChannelMass GNChannelBalance
  ring

/-- The depth mass is reconstructed from total mass and balance. -/
theorem GNChannelDepthMass_eq_half_mass_sub_balance
    (T : Triple) (p : ℕ) :
    GNChannelDepthMass T p =
      (GNChannelMass T p - GNChannelBalance T p) / 2 := by
  unfold GNChannelMass GNChannelBalance
  ring

/-- The existing affine channel budget is exactly a residual upper bound. -/
theorem GNNonExceptionalChannelMassBudgetAffine_iff_calibrationResidual_le
    (T : Triple) (p : ℕ) (ρ C : ℝ) :
    GNNonExceptionalChannelMassBudgetAffine T p ρ C ↔
      GNCalibrationResidual T p ρ ≤ C := by
  unfold GNNonExceptionalChannelMassBudgetAffine GNCalibrationResidual
    GNChannelMass GNChannelSupportMass GNChannelDepthMass Triple.radLog
  constructor <;> intro h <;> linarith

/--
At an odd prime exponent, joint pressure is exactly residual calibration.

This transports the existing production accounting equivalence; it does not
rebuild the lifted-radical argument.
-/
theorem Triple.oddPrimeJointPressure_iff_calibrationResidual_le
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNOddPrimeJointPressureBudgetAffine T p ρ C ↔
      GNCalibrationResidual T p ρ ≤ C := by
  rw [T.oddPrimeJointPressure_iff_nonExceptionalChannelMass hp ha hb]
  exact GNNonExceptionalChannelMassBudgetAffine_iff_calibrationResidual_le
    T p ρ C

/--
The existing intrinsic-epsilon correction can be consumed from the residual
coordinate directly.
-/
theorem Triple.abcEpsilon_le_GNEpsilon_add_correction_of_calibrationResidual_le
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hcal : GNCalibrationResidual T p ρ ≤ C) :
    T.abcEpsilon ≤
      GNEpsilon p ρ +
        (C + Real.log (rad p : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * T.radLog) := by
  apply T.abcEpsilon_le_GNEpsilon_add_correction hp hpOdd ha hb
  exact
    (T.oddPrimeJointPressure_iff_calibrationResidual_le hp ha hb).2 hcal

end DkMath.ABC
