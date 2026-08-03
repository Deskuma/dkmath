/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization
import DkMath.RH.Weave.Analytic.EtaPairPhaseSpan
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- Left endpoint of the natural eta-pair interval. -/
noncomputable def etaPairFrameLeftEndpoint (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℕ) : ℝ)

/-- Right endpoint of the natural eta-pair interval. -/
noncomputable def etaPairFrameRightEndpoint (k : ℕ) : ℝ :=
  ((2 * k + 2 : ℕ) : ℝ)

/-- The left endpoint of every natural eta-pair interval is positive. -/
theorem etaPairFrameLeftEndpoint_pos (k : ℕ) :
    0 < etaPairFrameLeftEndpoint k := by
  unfold etaPairFrameLeftEndpoint
  positivity

/-- The right endpoint of every natural eta-pair interval is positive. -/
theorem etaPairFrameRightEndpoint_pos (k : ℕ) :
    0 < etaPairFrameRightEndpoint k := by
  unfold etaPairFrameRightEndpoint
  positivity

/--
Unit rotation that removes the common phase at the left endpoint `2k+1`.

The common kernel has phase `-s.im * log x`, so the inverse base rotation is
`exp (I * s.im * log (2k+1))`.
-/
noncomputable def etaPairBaseRotation
    (s : ℂ) (k : ℕ) : ℂ :=
  Complex.exp
    (Complex.I *
      ((s.im * Real.log (etaPairFrameLeftEndpoint k) : ℝ) : ℂ))

/-- The eta-pair base rotation has unit norm. -/
theorem norm_etaPairBaseRotation
    (s : ℂ) (k : ℕ) :
    ‖etaPairBaseRotation s k‖ = 1 := by
  simp [etaPairBaseRotation]

/--
Residual real phase after removing the pair-left base angle.

For `x` in the pair interval this is
`s.im * (log x - log (2k+1))`.
-/
noncomputable def etaPairResidualPhase
    (s : ℂ) (k : ℕ) (x : ℝ) : ℝ :=
  s.im *
    (Real.log x - Real.log (etaPairFrameLeftEndpoint k))

/-- The unit residual rotation after pair-left derotation. -/
noncomputable def etaPairResidualRotation
    (s : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  Complex.exp
    (Complex.I * ((-etaPairResidualPhase s k x : ℝ) : ℂ))

/-- Every residual rotation has unit norm. -/
theorem norm_etaPairResidualRotation
    (s : ℂ) (k : ℕ) (x : ℝ) :
    ‖etaPairResidualRotation s k x‖ = 1 := by
  simp [etaPairResidualRotation]

/-- The real projection of the residual rotation is its residual cosine. -/
theorem etaPairResidualRotation_re
    (s : ℂ) (k : ℕ) (x : ℝ) :
    (etaPairResidualRotation s k x).re =
      Real.cos (etaPairResidualPhase s k x) := by
  simp [etaPairResidualRotation]

/--
Inside one natural eta-pair interval, the absolute residual phase is bounded
by the previously defined pair phase span.
-/
theorem abs_etaPairResidualPhase_le_phaseSpan
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k) :
    |etaPairResidualPhase s k x| ≤
      etaPairDerivativePhaseSpan s k := by
  have hleftPos : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hxPos : 0 < x := lt_of_lt_of_le hleftPos hleft
  have hrightPos : 0 < etaPairFrameRightEndpoint k :=
    etaPairFrameRightEndpoint_pos k
  have hlogNonneg :
      0 ≤ Real.log x - Real.log (etaPairFrameLeftEndpoint k) :=
    sub_nonneg.mpr (Real.log_le_log hleftPos hleft)
  have hlogUpper :
      Real.log x - Real.log (etaPairFrameLeftEndpoint k) ≤
        Real.log (etaPairFrameRightEndpoint k) -
          Real.log (etaPairFrameLeftEndpoint k) :=
    sub_le_sub_right (Real.log_le_log hxPos hright) _
  calc
    |etaPairResidualPhase s k x| =
        |s.im| *
          (Real.log x - Real.log (etaPairFrameLeftEndpoint k)) := by
      rw [etaPairResidualPhase, abs_mul, abs_of_nonneg hlogNonneg]
    _ ≤
        |s.im| *
          (Real.log (etaPairFrameRightEndpoint k) -
            Real.log (etaPairFrameLeftEndpoint k)) :=
      mul_le_mul_of_nonneg_left hlogUpper (abs_nonneg s.im)
    _ = etaPairDerivativePhaseSpan s k := by
      unfold etaPairDerivativePhaseSpan
      unfold etaPairFrameLeftEndpoint etaPairFrameRightEndpoint
      rw [Real.log_div (by positivity) (by positivity)]

/--
If the pair phase span is below `π/2`, every derotated residual phase in that
pair has strictly positive real projection.
-/
theorem etaPairResidualRotation_re_pos_of_span_lt_pi_div_two
    (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspan : etaPairDerivativePhaseSpan s k < Real.pi / 2) :
    0 < (etaPairResidualRotation s k x).re := by
  rw [etaPairResidualRotation_re]
  apply Real.cos_pos_of_mem_Ioo
  exact
    abs_lt.mp
      (lt_of_le_of_lt
        (abs_etaPairResidualPhase_le_phaseSpan s k hleft hright)
        hspan)

/--
Eventually every point of every eta-pair interval has positive real
projection in its own pair-left rotating frame.

This is a local sector theorem only.  It does not assert that the moving pair
frames share one global fixed half-plane.
-/
theorem eventually_etaPairResidualRotation_re_pos
    (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        0 < (etaPairResidualRotation s k x).re := by
  filter_upwards
    [eventually_etaPairDerivativePhaseSpan_lt_pi_div_two s] with k hspan
  intro x hleft hright
  exact
    etaPairResidualRotation_re_pos_of_span_lt_pi_div_two
      s k hleft hright hspan

end DkMath.RH.CFBRCProjection
