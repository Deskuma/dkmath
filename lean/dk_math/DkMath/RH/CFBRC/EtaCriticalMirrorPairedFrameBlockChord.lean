/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockAlignment
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockChord"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/--
The absolute signed phase accumulated across a finite pair-frame block is
exactly its total angular span.
-/
theorem abs_sum_range_etaPairFrameStepPhase_nat_add_eq_blockSpan
    (s : ℂ) (K N : ℕ) :
    |(Finset.range N).sum
        (fun j : ℕ => etaPairFrameStepPhase s (K + j))| =
      etaPairFrameBlockSpan s K N := by
  have hleft : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hright : 0 < etaPairFrameLeftEndpoint (K + N) :=
    etaPairFrameLeftEndpoint_pos (K + N)
  have horder :
      etaPairFrameLeftEndpoint K ≤
        etaPairFrameLeftEndpoint (K + N) := by
    unfold etaPairFrameLeftEndpoint
    exact_mod_cast (by omega : 2 * K + 1 ≤ 2 * (K + N) + 1)
  have hlog :
      0 ≤ Real.log (etaPairFrameLeftEndpoint (K + N)) -
        Real.log (etaPairFrameLeftEndpoint K) :=
    sub_nonneg.mpr (Real.log_le_log hleft horder)
  rw [sum_range_etaPairFrameStepPhase_nat_add,
    etaPairFrameBlockSpan_eq, abs_mul, abs_of_nonneg hlog]

/--
When a finite block span is at most one radian, the chord between its initial
and terminal pair frames is bounded linearly by twice that span.
-/
theorem norm_etaPairFrameBlockRotation_sub_one_le_two_mul_blockSpan
    (s : ℂ) (K N : ℕ)
    (hspan : etaPairFrameBlockSpan s K N ≤ 1) :
    ‖etaPairFrameBlockRotation s K N - 1‖ ≤
      2 * etaPairFrameBlockSpan s K N := by
  let z : ℂ :=
    Complex.I *
      ((((Finset.range N).sum
        (fun j : ℕ => etaPairFrameStepPhase s (K + j)) : ℝ) : ℂ))
  have hz :
      ‖z‖ =
        |(Finset.range N).sum
          (fun j : ℕ => etaPairFrameStepPhase s (K + j))| := by
    simp [z]
  rw [etaPairFrameBlockRotation_eq_exp]
  change ‖Complex.exp z - 1‖ ≤
    2 * etaPairFrameBlockSpan s K N
  calc
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
      apply Complex.norm_exp_sub_one_le
      rw [hz,
        abs_sum_range_etaPairFrameStepPhase_nat_add_eq_blockSpan]
      exact hspan
    _ = 2 * etaPairFrameBlockSpan s K N := by
      rw [hz,
        abs_sum_range_etaPairFrameStepPhase_nat_add_eq_blockSpan]

/-- For a fixed block length, the corresponding pair-frame chord tends to zero. -/
theorem norm_etaPairFrameBlockRotation_sub_one_tendsto_zero
    (s : ℂ) (N : ℕ) :
    Tendsto
      (fun K : ℕ => ‖etaPairFrameBlockRotation s K N - 1‖)
      atTop (nhds 0) := by
  have hupper :
      Tendsto
        (fun K : ℕ => 2 * etaPairFrameBlockSpan s K N)
        atTop (nhds 0) := by
    simpa using (etaPairFrameBlockSpan_tendsto_zero s N).const_mul 2
  have hbound :
      ∀ᶠ K : ℕ in atTop,
        ‖etaPairFrameBlockRotation s K N - 1‖ ≤
          2 * etaPairFrameBlockSpan s K N := by
    filter_upwards
      [(etaPairFrameBlockSpan_tendsto_zero s N).eventually_lt_const
        (by norm_num : (0 : ℝ) < 1)] with K hK
    exact
      norm_etaPairFrameBlockRotation_sub_one_le_two_mul_blockSpan
        s K N hK.le
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun K => norm_nonneg _)
      hbound

/-- The terminal frame of a finite block is its initial frame times the block rotation. -/
theorem etaPairBaseRotation_add_eq_mul_blockRotation
    (s : ℂ) (K N : ℕ) :
    etaPairBaseRotation s (K + N) =
      etaPairBaseRotation s K * etaPairFrameBlockRotation s K N := by
  rw [etaPairFrameBlockRotation_eq_exp]
  exact etaPairBaseRotation_add_eq s K N

/-- One defect pair viewed in the fixed frame at the beginning of its block. -/
noncomputable def etaCriticalMirrorBlockStartRotatedDefectPairTerm
    (s : ℂ) (K j : ℕ) : ℂ :=
  etaPairBaseRotation s K *
    etaCriticalMirrorDefectPairTerm s (K + j)

/--
The error between the block-start frame and the pair's own local frame is
controlled by the relative frame chord and the defect-pair norm.
-/
theorem norm_etaCriticalMirrorBlockStartRotatedDefectPairTerm_sub_local_le
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1) :
    ‖etaCriticalMirrorBlockStartRotatedDefectPairTerm s K j -
        etaCriticalMirrorRotatedDefectPairTerm s (K + j)‖ ≤
      2 * etaPairFrameBlockSpan s K j *
        ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ := by
  unfold etaCriticalMirrorBlockStartRotatedDefectPairTerm
  unfold etaCriticalMirrorRotatedDefectPairTerm
  rw [etaPairBaseRotation_add_eq_mul_blockRotation]
  have hfactor :
      etaPairBaseRotation s K *
          etaCriticalMirrorDefectPairTerm s (K + j) -
        (etaPairBaseRotation s K * etaPairFrameBlockRotation s K j) *
          etaCriticalMirrorDefectPairTerm s (K + j) =
        etaPairBaseRotation s K *
          ((1 - etaPairFrameBlockRotation s K j) *
            etaCriticalMirrorDefectPairTerm s (K + j)) := by
    ring
  rw [hfactor, norm_mul, norm_etaPairBaseRotation, one_mul, norm_mul]
  have hchord :
      ‖1 - etaPairFrameBlockRotation s K j‖ =
        ‖etaPairFrameBlockRotation s K j - 1‖ := by
    rw [show 1 - etaPairFrameBlockRotation s K j =
      -(etaPairFrameBlockRotation s K j - 1) by ring, norm_neg]
  rw [hchord]
  exact
    mul_le_mul_of_nonneg_right
      (norm_etaPairFrameBlockRotation_sub_one_le_two_mul_blockSpan
        s K j hspan)
      (norm_nonneg _)

end DkMath.RH.CFBRCProjection
