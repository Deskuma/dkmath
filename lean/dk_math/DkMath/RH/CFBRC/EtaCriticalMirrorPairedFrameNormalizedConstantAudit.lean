/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairMarginPowerLowerBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameVariation
import DkMath.RH.Weave.Analytic.EtaPairPhaseSpan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedConstantAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The terminal endpoint of a block beginning at `K` is the initial left endpoint
plus twice the block length and one final unit step.
-/
theorem etaPairFrameRightEndpoint_add_block_eq_leftEndpoint
    (K N : ℕ) :
    etaPairFrameRightEndpoint (K + N) =
      etaPairFrameLeftEndpoint K + 2 * (N : ℝ) + 1 := by
  unfold etaPairFrameRightEndpoint etaPairFrameLeftEndpoint
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

namespace EtaPairPositiveDensityBlockSchedule

/--
Ratio between the terminal endpoint of the scheduled block and the left
endpoint of its initial pair.
-/
noncomputable def endpointRatio
    (S : EtaPairPositiveDensityBlockSchedule) (K : ℕ) : ℝ :=
  etaPairFrameRightEndpoint (K + S.blockLength K) /
    etaPairFrameLeftEndpoint K

/-- Every scheduled endpoint ratio is strictly positive. -/
theorem endpointRatio_pos
    (S : EtaPairPositiveDensityBlockSchedule) (K : ℕ) :
    0 < S.endpointRatio K := by
  exact div_pos
    (etaPairFrameRightEndpoint_pos (K + S.blockLength K))
    (etaPairFrameLeftEndpoint_pos K)

/--
Exact decomposition of the endpoint ratio into the scheduled relative length
and the vanishing reciprocal endpoint correction.
-/
theorem endpointRatio_eq_one_add_two_mul_relativeLength_add_inv
    (S : EtaPairPositiveDensityBlockSchedule) (K : ℕ) :
    S.endpointRatio K =
      1 +
        2 *
          ((S.blockLength K : ℝ) /
            etaPairFrameLeftEndpoint K) +
        1 / etaPairFrameLeftEndpoint K := by
  unfold endpointRatio
  rw [etaPairFrameRightEndpoint_add_block_eq_leftEndpoint]
  have hleft : etaPairFrameLeftEndpoint K ≠ 0 :=
    (etaPairFrameLeftEndpoint_pos K).ne'
  field_simp [hleft]

/-- The reciprocal pair-left endpoint tends to zero. -/
theorem tendsto_one_div_etaPairFrameLeftEndpoint_zero :
    Tendsto
      (fun K : ℕ => (1 : ℝ) / etaPairFrameLeftEndpoint K)
      atTop (nhds 0) := by
  have hcomp :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      DkMath.RH.Weave.Analytic.tendsto_two_mul_add_one_atTop
  convert hcomp using 1
  funext K
  norm_num [etaPairFrameLeftEndpoint, Function.comp_apply,
    Nat.cast_add, Nat.cast_mul]

/--
For every positive-density schedule, the terminal-to-initial endpoint ratio
converges to `1 + 2ρ`.
-/
theorem endpointRatio_tendsto_one_add_two_mul_density
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto S.endpointRatio atTop
      (nhds (1 + 2 * S.density)) := by
  have hscaled :
      Tendsto
        (fun K : ℕ =>
          2 *
            ((S.blockLength K : ℝ) /
              etaPairFrameLeftEndpoint K))
        atTop (nhds (2 * S.density)) := by
    simpa using S.relativeLength_tendsto_density.const_mul 2
  have hsum :
      Tendsto
        (fun K : ℕ =>
          1 +
            2 *
              ((S.blockLength K : ℝ) /
                etaPairFrameLeftEndpoint K) +
            1 / etaPairFrameLeftEndpoint K)
        atTop
        (nhds ((1 + 2 * S.density) + 0)) :=
    (tendsto_const_nhds.add hscaled).add
      tendsto_one_div_etaPairFrameLeftEndpoint_zero
  convert hsum using 1
  · funext K
    exact
      endpointRatio_eq_one_add_two_mul_relativeLength_add_inv S K
  · ring_nf

/-- The endpoint-ratio limit is strictly positive. -/
theorem one_add_two_mul_density_pos
    (S : EtaPairPositiveDensityBlockSchedule) :
    0 < 1 + 2 * S.density := by
  linarith [S.density_pos]

/--
A fixed real power of the scheduled endpoint ratio converges to the same power
of `1 + 2ρ`. Positivity of the limiting ratio permits arbitrary real exponents.
-/
theorem endpointRatio_rpow_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) (q : ℝ) :
    Tendsto
      (fun K : ℕ => S.endpointRatio K ^ q)
      atTop
      (nhds ((1 + 2 * S.density) ^ q)) := by
  exact
    S.endpointRatio_tendsto_one_add_two_mul_density.rpow_const
      (Or.inl S.one_add_two_mul_density_pos.ne')

/--
Right-side normalized block-power factor before identifying it with the
normalized finite block lower bound.
-/
noncomputable def rightNormalizedBlockMarginPowerFactor
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) (K : ℕ) : ℝ :=
  (s.im ^ 2 / 4) *
    (((S.blockLength K : ℝ) /
        etaPairFrameLeftEndpoint K) *
      S.endpointRatio K ^ (s.re - 2))

/--
Left-side normalized block-power factor before identifying it with the
normalized finite block lower bound.
-/
noncomputable def leftNormalizedBlockMarginPowerFactor
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) (K : ℕ) : ℝ :=
  (s.im ^ 2 / 4) *
    (((S.blockLength K : ℝ) /
        etaPairFrameLeftEndpoint K) *
      S.endpointRatio K ^ (-s.re - 1))

/--
The right normalized block-power factor converges to its explicit density
constant.
-/
theorem rightNormalizedBlockMarginPowerFactor_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (S.rightNormalizedBlockMarginPowerFactor s)
      atTop
      (nhds
        ((s.im ^ 2 / 4) *
          (S.density *
            (1 + 2 * S.density) ^ (s.re - 2)))) := by
  simpa [rightNormalizedBlockMarginPowerFactor] using
    tendsto_const_nhds.mul
      (S.relativeLength_tendsto_density.mul
        (S.endpointRatio_rpow_tendsto (s.re - 2)))

/--
The left normalized block-power factor converges to its explicit density
constant.
-/
theorem leftNormalizedBlockMarginPowerFactor_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (S.leftNormalizedBlockMarginPowerFactor s)
      atTop
      (nhds
        ((s.im ^ 2 / 4) *
          (S.density *
            (1 + 2 * S.density) ^ (-s.re - 1)))) := by
  simpa [leftNormalizedBlockMarginPowerFactor] using
    tendsto_const_nhds.mul
      (S.relativeLength_tendsto_density.mul
        (S.endpointRatio_rpow_tendsto (-s.re - 1)))

/--
For the positive pair-left endpoint, the normalizing power `-1 - q` splits
into the reciprocal endpoint and the inverse `q`-power.
-/
theorem etaPairFrameLeftEndpoint_rpow_neg_one_sub
    (K : ℕ) (q : ℝ) :
    etaPairFrameLeftEndpoint K ^ (-1 - q) =
      (1 / etaPairFrameLeftEndpoint K) *
        (etaPairFrameLeftEndpoint K ^ q)⁻¹ := by
  rw [Real.rpow_sub (etaPairFrameLeftEndpoint_pos K) (-1) q]
  rw [Real.rpow_neg_one]
  simp [div_eq_mul_inv]

/--
The right normalized finite block lower bound is exactly the right density
power factor.
-/
theorem rightNormalizedBlockMarginPowerLowerBound_eq_factor
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) (K : ℕ) :
    etaPairFrameLeftEndpoint K ^ (1 - s.re) *
        etaCriticalMirrorRightBlockMarginPowerLowerBound
          s K (S.blockLength K) =
      S.rightNormalizedBlockMarginPowerFactor s K := by
  have hleft : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hright :
      0 < etaPairFrameRightEndpoint (K + S.blockLength K) :=
    etaPairFrameRightEndpoint_pos (K + S.blockLength K)
  have hnormalization :
      etaPairFrameLeftEndpoint K ^ (1 - s.re) =
        (1 / etaPairFrameLeftEndpoint K) *
          (etaPairFrameLeftEndpoint K ^ (s.re - 2))⁻¹ := by
    rw [show 1 - s.re = -1 - (s.re - 2) by ring]
    exact etaPairFrameLeftEndpoint_rpow_neg_one_sub K (s.re - 2)
  unfold etaCriticalMirrorRightBlockMarginPowerLowerBound
  unfold rightNormalizedBlockMarginPowerFactor endpointRatio
  rw [hnormalization, Real.div_rpow hright.le hleft.le]
  simp only [div_eq_mul_inv]
  ring

/--
The left normalized finite block lower bound is exactly the left density
power factor.
-/
theorem leftNormalizedBlockMarginPowerLowerBound_eq_factor
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) (K : ℕ) :
    etaPairFrameLeftEndpoint K ^ s.re *
        etaCriticalMirrorLeftBlockMarginPowerLowerBound
          s K (S.blockLength K) =
      S.leftNormalizedBlockMarginPowerFactor s K := by
  have hleft : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hright :
      0 < etaPairFrameRightEndpoint (K + S.blockLength K) :=
    etaPairFrameRightEndpoint_pos (K + S.blockLength K)
  have hnormalization :
      etaPairFrameLeftEndpoint K ^ s.re =
        (1 / etaPairFrameLeftEndpoint K) *
          (etaPairFrameLeftEndpoint K ^ (-s.re - 1))⁻¹ := by
    rw [show s.re = -1 - (-s.re - 1) by ring]
    exact etaPairFrameLeftEndpoint_rpow_neg_one_sub K (-s.re - 1)
  unfold etaCriticalMirrorLeftBlockMarginPowerLowerBound
  unfold leftNormalizedBlockMarginPowerFactor endpointRatio
  rw [hnormalization, Real.div_rpow hright.le hleft.le]
  simp only [div_eq_mul_inv]
  ring

/--
The actual right finite block lower bound, normalized by the pair-left scale,
converges to the right density constant.
-/
theorem rightNormalizedBlockMarginPowerLowerBound_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (1 - s.re) *
          etaCriticalMirrorRightBlockMarginPowerLowerBound
            s K (S.blockLength K))
      atTop
      (nhds
        ((s.im ^ 2 / 4) *
          (S.density *
            (1 + 2 * S.density) ^ (s.re - 2)))) := by
  simpa only [rightNormalizedBlockMarginPowerLowerBound_eq_factor] using
    S.rightNormalizedBlockMarginPowerFactor_tendsto s

/--
The actual left finite block lower bound, normalized by the pair-left scale,
converges to the left density constant.
-/
theorem leftNormalizedBlockMarginPowerLowerBound_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorLeftBlockMarginPowerLowerBound
            s K (S.blockLength K))
      atTop
      (nhds
        ((s.im ^ 2 / 4) *
          (S.density *
            (1 + 2 * S.density) ^ (-s.re - 1)))) := by
  simpa only [leftNormalizedBlockMarginPowerLowerBound_eq_factor] using
    S.leftNormalizedBlockMarginPowerFactor_tendsto s

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
