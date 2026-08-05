/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFixedLimitObstruction"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The chord of a relative block rotation is exactly the chord between its
terminal and initial base frames.  Unit norm of the initial frame removes the
common rotation factor.
-/
theorem norm_etaPairFrameBlockRotation_sub_one_eq_baseRotation_chord
    (s : ℂ) (K N : ℕ) :
    ‖etaPairFrameBlockRotation s K N - 1‖ =
      ‖etaPairBaseRotation s (K + N) - etaPairBaseRotation s K‖ := by
  rw [etaPairBaseRotation_add_eq_mul_blockRotation]
  have hfactor :
      etaPairBaseRotation s K * etaPairFrameBlockRotation s K N -
          etaPairBaseRotation s K =
        etaPairBaseRotation s K *
          (etaPairFrameBlockRotation s K N - 1) := by
    ring
  rw [hfactor, norm_mul, norm_etaPairBaseRotation, one_mul]

/--
If the base frames had a fixed limit, then the relative rotation from `K` to
`2K` would converge to the identity rotation.
-/
theorem etaPairHalfDensityBlockSchedule_scheduledBlockRotation_tendsto_one_of_baseRotation_tendsto
    {s L : ℂ}
    (hbase : Tendsto (etaPairBaseRotation s) atTop (nhds L)) :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockRotation s)
      atTop (nhds 1) := by
  have hindex :
      Tendsto (fun K : ℕ => K + K) atTop atTop := by
    apply StrictMono.tendsto_atTop
    intro K M hKM
    omega
  have hterminal :
      Tendsto
        (fun K : ℕ => etaPairBaseRotation s (K + K))
        atTop (nhds L) :=
    hbase.comp hindex
  have hdiff :
      Tendsto
        (fun K : ℕ =>
          etaPairBaseRotation s (K + K) - etaPairBaseRotation s K)
        atTop (nhds 0) := by
    convert hterminal.sub hbase using 1 <;> simp
  have hnorm :
      Tendsto
        (fun K : ℕ =>
          ‖etaPairBaseRotation s (K + K) - etaPairBaseRotation s K‖)
        atTop (nhds 0) := by
    simpa using (continuous_norm.tendsto 0).comp hdiff
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hnorm.congr' (Eventually.of_forall fun K => ?_)
  simpa [EtaPairPositiveDensityBlockSchedule.scheduledBlockRotation,
    etaPairHalfDensityBlockSchedule] using
    norm_etaPairFrameBlockRotation_sub_one_eq_baseRotation_chord s K K

/--
If the base frames had a fixed limit, then the relative rotation from `K` to
`3K` would also converge to the identity rotation.
-/
theorem etaPairFullDensityBlockSchedule_scheduledBlockRotation_tendsto_one_of_baseRotation_tendsto
    {s L : ℂ}
    (hbase : Tendsto (etaPairBaseRotation s) atTop (nhds L)) :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockRotation s)
      atTop (nhds 1) := by
  have hindex :
      Tendsto (fun K : ℕ => K + 2 * K) atTop atTop := by
    apply StrictMono.tendsto_atTop
    intro K M hKM
    omega
  have hterminal :
      Tendsto
        (fun K : ℕ => etaPairBaseRotation s (K + 2 * K))
        atTop (nhds L) :=
    hbase.comp hindex
  have hdiff :
      Tendsto
        (fun K : ℕ =>
          etaPairBaseRotation s (K + 2 * K) - etaPairBaseRotation s K)
        atTop (nhds 0) := by
    convert hterminal.sub hbase using 1 <;> simp
  have hnorm :
      Tendsto
        (fun K : ℕ =>
          ‖etaPairBaseRotation s (K + 2 * K) - etaPairBaseRotation s K‖)
        atTop (nhds 0) := by
    simpa using (continuous_norm.tendsto 0).comp hdiff
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hnorm.congr' (Eventually.of_forall fun K => ?_)
  simpa [EtaPairPositiveDensityBlockSchedule.scheduledBlockRotation,
    etaPairFullDensityBlockSchedule] using
    norm_etaPairFrameBlockRotation_sub_one_eq_baseRotation_chord s K (2 * K)

/--
At every nonzero imaginary height, the pair-left base rotation sequence has no
fixed complex limit.  Otherwise both the doubling and tripling relative
rotations would tend to one, contradicting two-scale nonresonance.
-/
theorem not_tendsto_etaPairBaseRotation_of_im_ne_zero
    {s L : ℂ} (him : s.im ≠ 0) :
    ¬ Tendsto (etaPairBaseRotation s) atTop (nhds L) := by
  intro hbase
  have hhalfOne :=
    etaPairHalfDensityBlockSchedule_scheduledBlockRotation_tendsto_one_of_baseRotation_tendsto
      hbase
  have hfullOne :=
    etaPairFullDensityBlockSchedule_scheduledBlockRotation_tendsto_one_of_baseRotation_tendsto
      hbase
  have hhalfExplicit :=
    etaPairHalfDensityBlockSchedule.scheduledBlockRotation_tendsto s
  have hfullExplicit :=
    etaPairFullDensityBlockSchedule.scheduledBlockRotation_tendsto s
  have hhalfEq :
      etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s = 1 :=
    tendsto_nhds_unique hhalfExplicit hhalfOne
  have hfullEq :
      etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s = 1 :=
    tendsto_nhds_unique hfullExplicit hfullOne
  rcases etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_ne_one him with
      hhalf | hfull
  · exact hhalf hhalfEq
  · exact hfull hfullEq

/-- No fixed asymptotic pair frame exists at a nonreal point. -/
theorem not_exists_etaPairBaseRotation_limit_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) :
    ¬ ∃ L : ℂ, Tendsto (etaPairBaseRotation s) atTop (nhds L) := by
  rintro ⟨L, hL⟩
  exact not_tendsto_etaPairBaseRotation_of_im_ne_zero him hL

/--
Named obstruction certificate: local frame increments vanish, but the base
frame has no fixed asymptotic limit.
-/
structure EtaPairFixedLimitObstructionCertificate (s : ℂ) : Prop where
  local_step_tendsto_zero :
    Tendsto (etaPairFrameStepSpan s) atTop (nhds 0)
  no_fixed_base_rotation_limit :
    ¬ ∃ L : ℂ, Tendsto (etaPairBaseRotation s) atTop (nhds L)

/-- Every nonreal point carries the fixed-limit obstruction certificate. -/
theorem etaPairFixedLimitObstructionCertificate_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) :
    EtaPairFixedLimitObstructionCertificate s :=
  ⟨etaPairFrameStepSpan_tendsto_zero s,
    not_exists_etaPairBaseRotation_limit_of_im_ne_zero him⟩

end DkMath.RH.CFBRCProjection
