/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABCBalanceCalibrationBridge

#print "file: DkMath.ABC.ABCCalibrationSourceDecomposition"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exact sources of the ABC/GN calibration correction

This module separates the exact pointwise calibration correction from the two
nonnegative proof-envelope slacks already present in the production route:
the GN return slack and the exceptional exponent-gauge slack.

The signed residual remains a pointwise mismatch with the chosen slope.  No
uniformization or optimization statement is made here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- Excess of `log GN` over the mandatory `(p - 1) * log c` return floor. -/
noncomputable def GNReturnSlack
    (T : Triple) (p : ℕ) : ℝ :=
  Real.log ((GN p T.a T.b : ℕ) : ℝ) -
    ((p - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)

/-- Allowance from replacing exact exceptional support by `rad p`. -/
noncomputable def GNExceptionalGaugeSlack
    (T : Triple) (p : ℕ) : ℝ :=
  Real.log (rad p : ℝ) -
    Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ)

/-- Exact pointwise calibration correction before the safe gauge envelope. -/
noncomputable def GNExactCalibrationCorrection
    (T : Triple) (p : ℕ) (ρ : ℝ) : ℝ :=
  (GNCalibrationResidual T p ρ +
      Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ) -
      GNReturnSlack T p) /
    (((p - 1 : ℕ) : ℝ) * T.radLog)

/-- The GN return slack is nonnegative on positive ABC inputs. -/
theorem GNReturnSlack_nonneg_of_prime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    0 ≤ GNReturnSlack T p := by
  unfold GNReturnSlack
  have hreturn := T.log_c_mul_pred_le_log_GN hp.two_le ha hb
  linarith

/-- The exceptional gauge slack is nonnegative for every positive exponent. -/
theorem GNExceptionalGaugeSlack_nonneg_of_one_le
    (T : Triple) {p : ℕ}
    (hp : 1 ≤ p) :
    0 ≤ GNExceptionalGaugeSlack T p := by
  unfold GNExceptionalGaugeSlack
  have hGauge :=
    log_GNExceptionalSupportProduct_le_log_rad
      (n := p) (a := T.a) (b := T.b) hp
  linarith

/-- Exact pointwise epsilon identity using the actual calibration sources. -/
theorem Triple.abcEpsilon_eq_GNEpsilon_add_exactCalibrationCorrection
    (T : Triple) {p : ℕ} {ρ : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcEpsilon =
      GNEpsilon p ρ + GNExactCalibrationCorrection T p ρ := by
  let d : ℝ := ((p - 1 : ℕ) : ℝ)
  let R : ℝ := T.radLog
  let S : ℝ := GNChannelSupportMass T p
  let E : ℝ := GNChannelDepthMass T p
  let M : ℝ := GNChannelMass T p
  let Cal : ℝ := GNCalibrationResidual T p ρ
  let X : ℝ := Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ)
  let G : ℝ := Real.log ((GN p T.a T.b : ℕ) : ℝ)
  let H : ℝ := Real.log (T.c : ℝ)
  let Ret : ℝ := GNReturnSlack T p
  have haccount :=
    T.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess
      hp hpOdd ha hb
  have haccount' : G = X + S + E := by
    change G = X + S + E at haccount
    exact haccount
  have hmain : d * H = X + ρ * R + Cal - Ret := by
    change d * H = X + ρ * R + (S + E - ρ * R) - (G - d * H)
    rw [haccount']
    ring
  have hquality := T.quality_eq_one_add_abcEpsilon ha hb
  change H / R = 1 + T.abcEpsilon at hquality
  have hnormalized : T.abcEpsilon = H / R - 1 := by
    linarith
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hR : 0 < R := by
    dsimp [R]
    simpa [Triple.radLog] using T.log_rad_abc_pos ha hb
  rw [hnormalized]
  dsimp [GNEpsilon, GNExactCalibrationCorrection]
  change H / R - 1 = ρ / d - 1 + (Cal + X - Ret) / (d * R)
  field_simp [ne_of_gt hd, ne_of_gt hR]
  linarith [hmain]

/-- The safe pointwise correction is exact correction plus both normalized slacks. -/
theorem GNPointwiseCalibrationCorrection_eq_exact_add_normalized_slack
    (T : Triple) (p : ℕ) (ρ : ℝ) :
    GNPointwiseCalibrationCorrection T p ρ =
      GNExactCalibrationCorrection T p ρ +
        (GNReturnSlack T p + GNExceptionalGaugeSlack T p) /
          (((p - 1 : ℕ) : ℝ) * T.radLog) := by
  unfold GNPointwiseCalibrationCorrection GNExactCalibrationCorrection
    GNExceptionalGaugeSlack
  ring

/-- The exact correction is below the safe pointwise envelope. -/
theorem GNExactCalibrationCorrection_le_pointwiseCalibrationCorrection
    (T : Triple) {p : ℕ} {ρ : ℝ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    GNExactCalibrationCorrection T p ρ ≤
      GNPointwiseCalibrationCorrection T p ρ := by
  have hret : 0 ≤ GNReturnSlack T p :=
    GNReturnSlack_nonneg_of_prime T hp ha hb
  have hGauge : 0 ≤ GNExceptionalGaugeSlack T p :=
    GNExceptionalGaugeSlack_nonneg_of_one_le T hp.one_le
  have hpred : 0 < (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hrad : 0 < T.radLog := by
    simpa [Triple.radLog] using T.log_rad_abc_pos ha hb
  have hden : 0 < (((p - 1 : ℕ) : ℝ) * T.radLog) :=
    mul_pos hpred hrad
  rw [GNPointwiseCalibrationCorrection_eq_exact_add_normalized_slack]
  have hslack :
      0 ≤ (GNReturnSlack T p + GNExceptionalGaugeSlack T p) /
        (((p - 1 : ℕ) : ℝ) * T.radLog) := by
    exact div_nonneg (add_nonneg hret hGauge) (le_of_lt hden)
  linarith

end DkMath.ABC
