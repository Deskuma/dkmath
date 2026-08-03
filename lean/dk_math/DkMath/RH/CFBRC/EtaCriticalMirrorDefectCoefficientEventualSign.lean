/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightThreshold
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientEventualSign"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/--
At a nonreal point, the pair-local phase error factor is eventually smaller
than the fixed vertical projection margin.
-/
private theorem eventually_defectCoefficient_rotation_factor_lt_vertical_margin
    (s : ℂ) (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      2 * |s.im| * (‖criticalMirror s‖ + ‖s‖) *
          etaPairDerivativePhaseSpan s k <
        s.im ^ 2 / 2 := by
  have hmargin : 0 < s.im ^ 2 / 2 := by
    positivity
  have hlim :
      Tendsto
        (fun k : ℕ =>
          (2 * |s.im| * (‖criticalMirror s‖ + ‖s‖)) *
            etaPairDerivativePhaseSpan s k)
        atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.const_mul
        (2 * |s.im| * (‖criticalMirror s‖ + ‖s‖))
        (etaPairDerivativePhaseSpan_tendsto_zero s))
  simpa [mul_assoc] using hlim.eventually_lt_const hmargin

/--
Right of the critical line, every sufficiently late eta pair has positive
signed vertical projection after its pair-local residual rotation.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_pos_on_pair
    {s : ℂ} (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        0 < etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) := by
  have hthreshold :=
    eventually_two_le_etaCriticalMirrorContinuousWeightR_on_pair_of_half_lt_re
      hre
  have hsmall :=
    eventually_defectCoefficient_rotation_factor_lt_vertical_margin s him
  have hspan :
      ∀ᶠ k : ℕ in atTop,
        etaPairDerivativePhaseSpan s k < 1 :=
    (etaPairDerivativePhaseSpan_tendsto_zero s).eventually_lt_const
      (by norm_num)
  filter_upwards [hthreshold, hsmall, hspan] with k hkWeight hkSmall hkSpan
  intro x hleft hright
  have hx : 0 < x :=
    (etaPairFrameLeftEndpoint_pos k).trans_le hleft
  have hweightPos :
      0 < etaCriticalMirrorContinuousWeightR s x :=
    etaCriticalMirrorContinuousWeightR_pos s hx
  have hsmallX :
      2 * |s.im| *
          ((‖criticalMirror s‖ + ‖s‖) *
            etaCriticalMirrorContinuousWeightR s x) *
          etaPairDerivativePhaseSpan s k <
        (s.im ^ 2 / 2) *
          etaCriticalMirrorContinuousWeightR s x := by
    have hm := mul_lt_mul_of_pos_right hkSmall hweightPos
    convert hm using 1 <;> ring
  exact
    etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_pos_of_right_margin
      s k hleft hright (le_of_lt hkSpan)
      (hkWeight x hleft hright) hsmallX

/--
Left of the critical line, every sufficiently late eta pair has negative
signed vertical projection after its pair-local residual rotation.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_neg_on_pair
    {s : ℂ} (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) < 0 := by
  have hthreshold :=
    eventually_etaCriticalMirrorContinuousWeightR_on_pair_le_half_of_re_lt_half
      hre
  have hsmall :=
    eventually_defectCoefficient_rotation_factor_lt_vertical_margin s him
  have hspan :
      ∀ᶠ k : ℕ in atTop,
        etaPairDerivativePhaseSpan s k < 1 :=
    (etaPairDerivativePhaseSpan_tendsto_zero s).eventually_lt_const
      (by norm_num)
  filter_upwards [hthreshold, hsmall, hspan] with k hkWeight hkSmall hkSpan
  intro x hleft hright
  exact
    etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_neg_of_left_margin
      s k hleft hright (le_of_lt hkSpan)
      (hkWeight x hleft hright) hkSmall

end DkMath.RH.CFBRCProjection
