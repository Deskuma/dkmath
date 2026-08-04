/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedConstantAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedConstantAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedConstantAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (K N : ℕ) :
    etaPairFrameRightEndpoint (K + N) =
      etaPairFrameLeftEndpoint K + 2 * (N : ℝ) + 1 :=
  etaPairFrameRightEndpoint_add_block_eq_leftEndpoint K N

example
    (S : EtaPairPositiveDensityBlockSchedule) (K : ℕ) :
    S.endpointRatio K =
      1 +
        2 *
          ((S.blockLength K : ℝ) /
            etaPairFrameLeftEndpoint K) +
        1 / etaPairFrameLeftEndpoint K :=
  S.endpointRatio_eq_one_add_two_mul_relativeLength_add_inv K

example :
    Tendsto
      (fun K : ℕ => (1 : ℝ) / etaPairFrameLeftEndpoint K)
      atTop (nhds 0) :=
  EtaPairPositiveDensityBlockSchedule.tendsto_one_div_etaPairFrameLeftEndpoint_zero

example
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto S.endpointRatio atTop
      (nhds (1 + 2 * S.density)) :=
  S.endpointRatio_tendsto_one_add_two_mul_density

example
    (S : EtaPairPositiveDensityBlockSchedule) :
    0 < 1 + 2 * S.density :=
  S.one_add_two_mul_density_pos

example
    (S : EtaPairPositiveDensityBlockSchedule) (q : ℝ) :
    Tendsto
      (fun K : ℕ => S.endpointRatio K ^ q)
      atTop
      (nhds ((1 + 2 * S.density) ^ q)) :=
  S.endpointRatio_rpow_tendsto q

example
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (S.rightNormalizedBlockMarginPowerFactor s)
      atTop
      (nhds
        ((s.im ^ 2 / 4) *
          (S.density *
            (1 + 2 * S.density) ^ (s.re - 2)))) :=
  S.rightNormalizedBlockMarginPowerFactor_tendsto s

example
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (S.leftNormalizedBlockMarginPowerFactor s)
      atTop
      (nhds
        ((s.im ^ 2 / 4) *
          (S.density *
            (1 + 2 * S.density) ^ (-s.re - 1)))) :=
  S.leftNormalizedBlockMarginPowerFactor_tendsto s

example (K : ℕ) (q : ℝ) :
    etaPairFrameLeftEndpoint K ^ (-1 - q) =
      (1 / etaPairFrameLeftEndpoint K) *
        (etaPairFrameLeftEndpoint K ^ q)⁻¹ :=
  EtaPairPositiveDensityBlockSchedule.etaPairFrameLeftEndpoint_rpow_neg_one_sub K q

example
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) (K : ℕ) :
    etaPairFrameLeftEndpoint K ^ (1 - s.re) *
        etaCriticalMirrorRightBlockMarginPowerLowerBound
          s K (S.blockLength K) =
      S.rightNormalizedBlockMarginPowerFactor s K :=
  S.rightNormalizedBlockMarginPowerLowerBound_eq_factor s K

example
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) (K : ℕ) :
    etaPairFrameLeftEndpoint K ^ s.re *
        etaCriticalMirrorLeftBlockMarginPowerLowerBound
          s K (S.blockLength K) =
      S.leftNormalizedBlockMarginPowerFactor s K :=
  S.leftNormalizedBlockMarginPowerLowerBound_eq_factor s K

example
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
            (1 + 2 * S.density) ^ (s.re - 2)))) :=
  S.rightNormalizedBlockMarginPowerLowerBound_tendsto s

example
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
            (1 + 2 * S.density) ^ (-s.re - 1)))) :=
  S.leftNormalizedBlockMarginPowerLowerBound_tendsto s

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedConstantAudit
