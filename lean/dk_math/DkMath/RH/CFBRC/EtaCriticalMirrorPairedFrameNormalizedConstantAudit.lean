/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairMarginPowerLowerBound
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
  ring

/-- The reciprocal pair-left endpoint tends to zero. -/
theorem tendsto_one_div_etaPairFrameLeftEndpoint_zero :
    Tendsto
      (fun K : ℕ => (1 : ℝ) / etaPairFrameLeftEndpoint K)
      atTop (nhds 0) := by
  have hcomp :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      tendsto_two_mul_add_one_atTop
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
  · ring

/-- The endpoint-ratio limit is strictly positive. -/
theorem one_add_two_mul_density_pos
    (S : EtaPairPositiveDensityBlockSchedule) :
    0 < 1 + 2 * S.density := by
  linarith [S.density_pos]

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
