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

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedConstantAudit
