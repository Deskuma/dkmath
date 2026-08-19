/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityRotationLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockGeometry
import Mathlib.Tactic

/-!
# ZDI-007: positive-density schedule compatibility audit

This module formalizes the first compatibility check required by ZDI-007.
The existing growing-block geometry requires relative block length tending to
zero, while a positive-density schedule requires the same ratio to tend to a
strictly positive density.  The two contracts cannot describe the same block
length function.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

namespace EtaPairPositiveDensityBlockSchedule

/--
A positive-density schedule cannot also have its relative block length tend
to zero.  This is a limit incompatibility, independent of zeta zeros and of
the residual/margin constants.
-/
theorem not_relativeLength_tendsto_zero
    (S : EtaPairPositiveDensityBlockSchedule)
    (hzero :
      Tendsto
        (fun K : ℕ =>
          (S.blockLength K : ℝ) / etaPairFrameLeftEndpoint K)
        atTop (nhds 0)) :
    False := by
  have hlimits := tendsto_nhds_unique hzero S.relativeLength_tendsto_density
  linarith [S.density_pos]

/--
No block function can simultaneously instantiate the positive-density and
the existing sublinear growing-block schedule contracts.
-/
theorem not_common_blockLength_with_etaPairGrowingBlockSchedule
    (P : EtaPairPositiveDensityBlockSchedule)
    (G : EtaPairGrowingBlockSchedule)
    (hblock : P.blockLength = G.blockLength) :
    False := by
  apply P.not_relativeLength_tendsto_zero
  simpa [hblock] using G.relativeLength_tendsto_zero

/--
Positive density produces a nonzero limiting block-frame span in general.  Its
limit is the absolute imaginary height times `log (1 + 2 * density)`, so the
sublinear frame-span-to-zero theorem cannot be reused for this schedule.
-/
theorem blockSpan_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameBlockSpan s K (S.blockLength K))
      atTop
      (nhds (|s.im| * Real.log (1 + 2 * S.density))) := by
  have hratio := S.leftEndpointRatio_tendsto_one_add_two_mul_density
  have hlog := hratio.log S.one_add_two_mul_density_pos.ne'
  have hmul :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => |s.im|) atTop (nhds |s.im|)).mul hlog
  rw [show
      (fun K : ℕ => etaPairFrameBlockSpan s K (S.blockLength K)) =
        (fun K : ℕ => |s.im| * Real.log (S.leftEndpointRatio K)) by
      funext K
      rw [etaPairFrameBlockSpan_eq]
      rw [← Real.log_div
        (etaPairFrameLeftEndpoint_pos
          (K + S.blockLength K)).ne'
        (etaPairFrameLeftEndpoint_pos K).ne']
      rfl]
  simpa [mul_assoc] using hmul

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
