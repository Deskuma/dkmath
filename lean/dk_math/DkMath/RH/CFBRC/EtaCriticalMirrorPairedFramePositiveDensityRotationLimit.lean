/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedConstantAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockAlignment
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityRotationLimit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/-- The left endpoint after a block of length `N` is shifted by exactly `2N`. -/
theorem etaPairFrameLeftEndpoint_add_block_eq
    (K N : ℕ) :
    etaPairFrameLeftEndpoint (K + N) =
      etaPairFrameLeftEndpoint K + 2 * (N : ℝ) := by
  unfold etaPairFrameLeftEndpoint
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

namespace EtaPairPositiveDensityBlockSchedule

/-- Ratio of the terminal pair-left endpoint to the initial pair-left endpoint. -/
noncomputable def leftEndpointRatio
    (S : EtaPairPositiveDensityBlockSchedule) (K : ℕ) : ℝ :=
  etaPairFrameLeftEndpoint (K + S.blockLength K) /
    etaPairFrameLeftEndpoint K

/-- Exact decomposition of the pair-left endpoint ratio. -/
theorem leftEndpointRatio_eq_one_add_two_mul_relativeLength
    (S : EtaPairPositiveDensityBlockSchedule) (K : ℕ) :
    S.leftEndpointRatio K =
      1 +
        2 *
          ((S.blockLength K : ℝ) /
            etaPairFrameLeftEndpoint K) := by
  unfold leftEndpointRatio
  rw [etaPairFrameLeftEndpoint_add_block_eq]
  have hleft : etaPairFrameLeftEndpoint K ≠ 0 :=
    (etaPairFrameLeftEndpoint_pos K).ne'
  field_simp [hleft]
  ring

/-- Every positive-density schedule has pair-left endpoint ratio `1 + 2ρ`. -/
theorem leftEndpointRatio_tendsto_one_add_two_mul_density
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto S.leftEndpointRatio atTop
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
                etaPairFrameLeftEndpoint K))
        atTop (nhds (1 + 2 * S.density)) :=
    tendsto_const_nhds.add hscaled
  convert hsum using 1
  funext K
  exact S.leftEndpointRatio_eq_one_add_two_mul_relativeLength K

/-- Signed frame phase accumulated across the scheduled positive-density block. -/
noncomputable def scheduledBlockPhase
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) (K : ℕ) : ℝ :=
  (Finset.range (S.blockLength K)).sum
    (fun j : ℕ => etaPairFrameStepPhase s (K + j))

/-- The scheduled block phase is the imaginary height times the log endpoint ratio. -/
theorem scheduledBlockPhase_eq_im_mul_log_leftEndpointRatio
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) (K : ℕ) :
    S.scheduledBlockPhase s K =
      s.im * Real.log (S.leftEndpointRatio K) := by
  unfold scheduledBlockPhase leftEndpointRatio
  rw [sum_range_etaPairFrameStepPhase_nat_add]
  rw [← Real.log_div
    (etaPairFrameLeftEndpoint_pos (K + S.blockLength K)).ne'
    (etaPairFrameLeftEndpoint_pos K).ne']

/-- The lifted signed phase across a positive-density block has an explicit limit. -/
theorem scheduledBlockPhase_tendsto
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) :
    Tendsto
      (S.scheduledBlockPhase s)
      atTop
      (nhds
        (s.im * Real.log (1 + 2 * S.density))) := by
  have hratio := S.leftEndpointRatio_tendsto_one_add_two_mul_density
  have hlog := hratio.log S.one_add_two_mul_density_pos.ne'
  have hmul := tendsto_const_nhds.mul hlog
  simpa only [S.scheduledBlockPhase_eq_im_mul_log_leftEndpointRatio]
    using hmul

/-- Relative frame rotation across the scheduled positive-density block. -/
noncomputable def scheduledBlockRotation
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) (K : ℕ) : ℂ :=
  etaPairFrameBlockRotation s K (S.blockLength K)

/-- Explicit unit-complex limit of the positive-density block rotation. -/
noncomputable def scheduledBlockRotationLimit
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) : ℂ :=
  Complex.exp
    (Complex.I *
      (((s.im * Real.log (1 + 2 * S.density) : ℝ) : ℂ)))

/-- Positive-density relative frame rotations converge to their explicit phase limit. -/
theorem scheduledBlockRotation_tendsto
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) :
    Tendsto
      (S.scheduledBlockRotation s)
      atTop
      (nhds (S.scheduledBlockRotationLimit s)) := by
  have hphase := S.scheduledBlockPhase_tendsto s
  have hcast :
      Tendsto
        (fun K : ℕ => ((S.scheduledBlockPhase s K : ℝ) : ℂ))
        atTop
        (nhds
          (((s.im * Real.log (1 + 2 * S.density) : ℝ) : ℂ))) := by
    have h :=
      (Complex.continuous_ofReal.tendsto
        (s.im * Real.log (1 + 2 * S.density))).comp hphase
    simpa [Function.comp_def] using h
  have hinner :
      Tendsto
        (fun K : ℕ =>
          Complex.I * ((S.scheduledBlockPhase s K : ℝ) : ℂ))
        atTop
        (nhds
          (Complex.I *
            (((s.im * Real.log (1 + 2 * S.density) : ℝ) : ℂ)))) := by
    simpa using tendsto_const_nhds.mul hcast
  have hexp :=
    (Complex.continuous_exp.tendsto
      (Complex.I *
        (((s.im * Real.log (1 + 2 * S.density) : ℝ) : ℂ)))).comp
      hinner
  simpa [scheduledBlockRotation, scheduledBlockRotationLimit,
    etaPairFrameBlockRotation_eq_exp, scheduledBlockPhase,
    Function.comp_def] using hexp

/-- For the canonical block `N(K)=K`, the limiting relative phase is `s.im * log 2`. -/
theorem etaPairHalfDensityBlockSchedule_scheduledBlockPhase_tendsto
    (s : ℂ) :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockPhase s)
      atTop
      (nhds (s.im * Real.log 2)) := by
  simpa using etaPairHalfDensityBlockSchedule.scheduledBlockPhase_tendsto s

/-- For the canonical block `N(K)=K`, the relative rotation tends to `exp(I * s.im * log 2)`. -/
theorem etaPairHalfDensityBlockSchedule_scheduledBlockRotation_tendsto
    (s : ℂ) :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockRotation s)
      atTop
      (nhds
        (Complex.exp
          (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))))) := by
  simpa [scheduledBlockRotationLimit] using
    etaPairHalfDensityBlockSchedule.scheduledBlockRotation_tendsto s

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
