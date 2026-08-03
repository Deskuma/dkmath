/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectDecay
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- One paired mirror defect viewed in its pair-left rotating frame. -/
noncomputable def etaCriticalMirrorRotatedDefectPairTerm
    (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k

/-- Finite sum of paired mirror defects in their moving pair-local frames. -/
noncomputable def etaCriticalMirrorRotatedDefectPairedPartial
    (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum (etaCriticalMirrorRotatedDefectPairTerm s)

/-- Boundary term appearing after summation by parts. -/
noncomputable def etaCriticalMirrorPairedAbelBoundaryTerm
    (K : ℕ) (s : ℂ) : ℂ :=
  etaPairBaseRotation s (K - 1) *
    etaCriticalMirrorDefectPairedPartial K s

/-- Frame-motion correction term appearing after summation by parts. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionTerm
    (s : ℂ) (k : ℕ) : ℂ :=
  (etaPairBaseRotation s (k + 1) - etaPairBaseRotation s k) *
    etaCriticalMirrorDefectPairedPartial (k + 1) s

/--
Exact finite Abel transformation for the moving-frame paired defect sum.

The moving local rotations are transferred from the individual defect pairs
to one terminal boundary term and a finite sum of adjacent frame-motion
corrections.  This is a purely finite identity and uses no limit theorem.
-/
theorem etaCriticalMirrorRotatedDefectPairedPartial_eq_abel
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorRotatedDefectPairedPartial K s =
      etaCriticalMirrorPairedAbelBoundaryTerm K s -
        (Finset.range (K - 1)).sum
          (etaCriticalMirrorPairedFrameCorrectionTerm s) := by
  simpa [etaCriticalMirrorRotatedDefectPairedPartial,
    etaCriticalMirrorRotatedDefectPairTerm,
    etaCriticalMirrorPairedAbelBoundaryTerm,
    etaCriticalMirrorPairedFrameCorrectionTerm,
    etaCriticalMirrorDefectPairedPartial, smul_eq_mul] using
    (Finset.sum_range_by_parts
      (etaPairBaseRotation s)
      (etaCriticalMirrorDefectPairTerm s)
      K)

/-- The Abel boundary rotation does not change the defect-partial norm. -/
theorem norm_etaCriticalMirrorPairedAbelBoundaryTerm
    (K : ℕ) (s : ℂ) :
    ‖etaCriticalMirrorPairedAbelBoundaryTerm K s‖ =
      ‖etaCriticalMirrorDefectPairedPartial K s‖ := by
  rw [etaCriticalMirrorPairedAbelBoundaryTerm, norm_mul,
    norm_etaPairBaseRotation, one_mul]

/--
A small adjacent frame angle gives a linear bound on the corresponding unit
circle chord.  The constant `2` comes from Mathlib's local exponential bound.
-/
theorem norm_etaPairBaseRotation_succ_sub_le_two_mul_stepSpan
    (s : ℂ) (k : ℕ)
    (hspan : etaPairFrameStepSpan s k ≤ 1) :
    ‖etaPairBaseRotation s (k + 1) - etaPairBaseRotation s k‖ ≤
      2 * etaPairFrameStepSpan s k := by
  let z : ℂ :=
    Complex.I * ((etaPairFrameStepPhase s k : ℝ) : ℂ)
  have hz : ‖z‖ = etaPairFrameStepSpan s k := by
    simp [z, abs_etaPairFrameStepPhase]
  rw [etaPairBaseRotation_succ]
  change
    ‖etaPairBaseRotation s k * Complex.exp z -
        etaPairBaseRotation s k‖ ≤
      2 * etaPairFrameStepSpan s k
  calc
    ‖etaPairBaseRotation s k * Complex.exp z -
        etaPairBaseRotation s k‖ =
        ‖etaPairBaseRotation s k * (Complex.exp z - 1)‖ := by
      congr 1
      ring
    _ = ‖Complex.exp z - 1‖ := by
      rw [norm_mul, norm_etaPairBaseRotation, one_mul]
    _ ≤ 2 * ‖z‖ :=
      Complex.norm_exp_sub_one_le (by simpa [hz] using hspan)
    _ = 2 * etaPairFrameStepSpan s k := by rw [hz]

/-- Eventually every adjacent pair-frame chord obeys the linear step-span bound. -/
theorem eventually_norm_etaPairBaseRotation_succ_sub_le_two_mul_stepSpan
    (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      ‖etaPairBaseRotation s (k + 1) - etaPairBaseRotation s k‖ ≤
        2 * etaPairFrameStepSpan s k := by
  filter_upwards
    [(etaPairFrameStepSpan_tendsto_zero s).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)] with k hk
  exact
    norm_etaPairBaseRotation_succ_sub_le_two_mul_stepSpan
      s k hk.le

/--
The norm of one Abel correction is bounded by the frame chord times the norm
of the corresponding paired defect partial sum.
-/
theorem norm_etaCriticalMirrorPairedFrameCorrectionTerm_le
    (s : ℂ) (k : ℕ)
    (hspan : etaPairFrameStepSpan s k ≤ 1) :
    ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
      2 * etaPairFrameStepSpan s k *
        ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ := by
  rw [etaCriticalMirrorPairedFrameCorrectionTerm, norm_mul]
  exact
    mul_le_mul_of_nonneg_right
      (norm_etaPairBaseRotation_succ_sub_le_two_mul_stepSpan
        s k hspan)
      (norm_nonneg _)

end DkMath.RH.CFBRCProjection
