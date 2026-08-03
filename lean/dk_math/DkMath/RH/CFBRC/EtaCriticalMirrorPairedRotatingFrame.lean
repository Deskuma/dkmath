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
  rw [etaPairBaseRotation, Complex.norm_exp]
  simp

/-- Real angular increment from the `k`-th pair frame to the next one. -/
noncomputable def etaPairFrameStepPhase
    (s : ℂ) (k : ℕ) : ℝ :=
  s.im *
    (Real.log (etaPairFrameLeftEndpoint (k + 1)) -
      Real.log (etaPairFrameLeftEndpoint k))

/-- Absolute angular increment between two adjacent pair frames. -/
noncomputable def etaPairFrameStepSpan
    (s : ℂ) (k : ℕ) : ℝ :=
  |s.im| *
    Real.log
      (etaPairFrameLeftEndpoint (k + 1) /
        etaPairFrameLeftEndpoint k)

/-- The next pair frame is obtained by the exact adjacent frame-step rotation. -/
theorem etaPairBaseRotation_succ
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation s (k + 1) =
      etaPairBaseRotation s k *
        Complex.exp
          (Complex.I *
            ((etaPairFrameStepPhase s k : ℝ) : ℂ)) := by
  rw [etaPairBaseRotation, etaPairBaseRotation, ← Complex.exp_add]
  congr 1
  rw [etaPairFrameStepPhase]
  push_cast
  ring

/-- The frame-step span is exactly the absolute adjacent phase increment. -/
theorem abs_etaPairFrameStepPhase
    (s : ℂ) (k : ℕ) :
    |etaPairFrameStepPhase s k| =
      etaPairFrameStepSpan s k := by
  have ha : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hb : 0 < etaPairFrameLeftEndpoint (k + 1) :=
    etaPairFrameLeftEndpoint_pos (k + 1)
  have hab :
      etaPairFrameLeftEndpoint k ≤
        etaPairFrameLeftEndpoint (k + 1) := by
    unfold etaPairFrameLeftEndpoint
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1)
  have hlogNonneg :
      0 ≤
        Real.log (etaPairFrameLeftEndpoint (k + 1)) -
          Real.log (etaPairFrameLeftEndpoint k) :=
    sub_nonneg.mpr (Real.log_le_log ha hab)
  rw [etaPairFrameStepPhase, etaPairFrameStepSpan, abs_mul,
    abs_of_nonneg hlogNonneg, Real.log_div hb.ne' ha.ne']

/-- The adjacent frame-step span is always nonnegative. -/
theorem etaPairFrameStepSpan_nonneg
    (s : ℂ) (k : ℕ) :
    0 ≤ etaPairFrameStepSpan s k := by
  rw [← abs_etaPairFrameStepPhase]
  exact abs_nonneg _

/--
The adjacent pair-frame angle is bounded by twice the reciprocal left
endpoint.  Unlike the in-pair phase width, the frame moves across two integer
steps: `(2k+1) → (2k+3)`.
-/
theorem etaPairFrameStepSpan_le_two_mul_inv
    (s : ℂ) (k : ℕ) :
    etaPairFrameStepSpan s k ≤
      2 *
        (|s.im| / etaPairFrameLeftEndpoint k) := by
  let a : ℝ := etaPairFrameLeftEndpoint k
  let b : ℝ := etaPairFrameLeftEndpoint (k + 1)
  have ha : 0 < a := by
    dsimp [a]
    exact etaPairFrameLeftEndpoint_pos k
  have hb : 0 < b := by
    dsimp [b]
    exact etaPairFrameLeftEndpoint_pos (k + 1)
  have hstep : b = a + 2 := by
    dsimp [a, b, etaPairFrameLeftEndpoint]
    norm_num
    ring
  have hlog : Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hratio : b / a - 1 = 2 / a := by
    rw [hstep]
    field_simp [ha.ne']
    ring
  rw [hratio] at hlog
  unfold etaPairFrameStepSpan
  change |s.im| * Real.log (b / a) ≤ 2 * (|s.im| / a)
  calc
    |s.im| * Real.log (b / a) ≤
        |s.im| * (2 / a) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg s.im)
    _ = 2 * (|s.im| / a) := by ring

/-- Adjacent eta-pair frame increments shrink to zero. -/
theorem etaPairFrameStepSpan_tendsto_zero
    (s : ℂ) :
    Tendsto (fun k : ℕ => etaPairFrameStepSpan s k)
      atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun k : ℕ =>
          |s.im| / etaPairFrameLeftEndpoint k)
        atTop (nhds 0) := by
    have hcomp :=
      (tendsto_const_div_atTop_nhds_zero_nat (|s.im| : ℝ)).comp
        tendsto_two_mul_add_one_atTop
    convert hcomp using 1
    funext k
    norm_num [etaPairFrameLeftEndpoint, Function.comp_apply,
      Nat.cast_add, Nat.cast_mul]
  have hupper :
      Tendsto
        (fun k : ℕ =>
          2 * (|s.im| / etaPairFrameLeftEndpoint k))
        atTop (nhds 0) := by
    simpa using hbase.const_mul 2
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k =>
        etaPairFrameStepSpan_nonneg s k)
      (Eventually.of_forall fun k =>
        etaPairFrameStepSpan_le_two_mul_inv s k)

/-- Eventually adjacent pair frames differ by less than a half-plane angle. -/
theorem eventually_etaPairFrameStepSpan_lt_pi_div_two
    (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      etaPairFrameStepSpan s k < Real.pi / 2 :=
  (etaPairFrameStepSpan_tendsto_zero s).eventually_lt_const
    (by positivity)

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
  rw [etaPairResidualRotation, Complex.norm_exp]
  simp

/-- The real projection of the residual rotation is its residual cosine. -/
theorem etaPairResidualRotation_re
    (s : ℂ) (k : ℕ) (x : ℝ) :
    (etaPairResidualRotation s k x).re =
      Real.cos (etaPairResidualPhase s k x) := by
  rw [etaPairResidualRotation, Complex.exp_re]
  simp

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
