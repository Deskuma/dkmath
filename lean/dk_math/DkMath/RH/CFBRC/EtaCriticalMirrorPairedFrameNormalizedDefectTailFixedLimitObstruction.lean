/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFixedLimitObstruction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Index-normalized unrotated critical-mirror defect tail. -/
noncomputable def etaCriticalMirrorIndexNormalizedDefectTail
    (a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
    etaCriticalMirrorDefectPairTail (k + 1) s

/-- The same normalized defect tail transported into its pair-left frame. -/
noncomputable def etaCriticalMirrorIndexNormalizedRotatedDefectTail
    (a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
    etaCriticalMirrorPairFrameRotatedDefectTail s k

/-- Rotating the normalized unrotated tail gives the normalized rotated tail. -/
theorem etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedDefectTail a s k =
      etaPairBaseRotation s k *
        etaCriticalMirrorIndexNormalizedDefectTail a s k := by
  unfold etaCriticalMirrorIndexNormalizedRotatedDefectTail
  unfold etaCriticalMirrorIndexNormalizedDefectTail
  unfold etaCriticalMirrorPairFrameRotatedDefectTail
  ring

/-- Rotation preserves the norm of every index-normalized defect tail. -/
theorem norm_etaCriticalMirrorIndexNormalizedRotatedDefectTail
    (a : ℝ) (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorIndexNormalizedRotatedDefectTail a s k‖ =
      ‖etaCriticalMirrorIndexNormalizedDefectTail a s k‖ := by
  rw [etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul,
    norm_mul, norm_etaPairBaseRotation, one_mul]

/-- The explicit Euler half-tail constant never vanishes. -/
theorem etaPairIndexNormalizedTailConstant_ne_zero
    (z : ℂ) :
    etaPairIndexNormalizedTailConstant z ≠ 0 := by
  unfold etaPairIndexNormalizedTailConstant
  apply mul_ne_zero
  · norm_num
  · exact_mod_cast
      (Real.rpow_pos_of_pos (by norm_num : 0 < (1 : ℝ) / 2) z.re).ne'

/--
If a unit rotation of a sequence tends to a nonzero limit, then any fixed
limit of the unrotated sequence must also be nonzero.
-/
private theorem normalizedDefectTail_limit_ne_zero_of_rotated_limit_ne_zero
    {B D Z : ℕ → ℂ} {L C : ℂ}
    (hunit : ∀ k : ℕ, ‖B k‖ = 1)
    (hfactor : ∀ k : ℕ, Z k = B k * D k)
    (hD : Tendsto D atTop (nhds L))
    (hZ : Tendsto Z atTop (nhds C))
    (hC : C ≠ 0) :
    L ≠ 0 := by
  intro hL
  subst L
  have hDnorm :
      Tendsto (fun k : ℕ => ‖D k‖) atTop (nhds 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ)).comp hD
  have hZnorm :
      Tendsto (fun k : ℕ => ‖Z k‖) atTop (nhds 0) := by
    refine hDnorm.congr' (Eventually.of_forall fun k => ?_)
    rw [hfactor k, norm_mul, hunit k, one_mul]
  have hZzero : Tendsto Z atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hZnorm
  exact hC (tendsto_nhds_unique hZ hZzero)

/--
A nonzero fixed limit of the rotated normalized tail and a hypothetical fixed
limit of the unrotated normalized tail would reconstruct a fixed limit of the
base rotation.  This contradicts the two-scale fixed-frame obstruction.
-/
theorem not_tendsto_etaCriticalMirrorIndexNormalizedDefectTail_of_rotated_limit
    {a : ℝ} {s C L : ℂ}
    (him : s.im ≠ 0)
    (hrot :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail a s)
        atTop (nhds C))
    (hC : C ≠ 0) :
    ¬ Tendsto
      (etaCriticalMirrorIndexNormalizedDefectTail a s)
      atTop (nhds L) := by
  intro htail
  have hL : L ≠ 0 :=
    normalizedDefectTail_limit_ne_zero_of_rotated_limit_ne_zero
      (fun k => norm_etaPairBaseRotation s k)
      (fun k =>
        etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul
          a s k)
      htail hrot hC
  have htailNe :
      ∀ᶠ k : ℕ in atTop,
        etaCriticalMirrorIndexNormalizedDefectTail a s k ≠ 0 := by
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp htail
    have hclose :=
      hnorm.eventually_lt_const (norm_pos_iff.mpr hL)
    filter_upwards [hclose] with k hk
    intro hkZero
    rw [hkZero, zero_sub, norm_neg] at hk
    exact (lt_irrefl _ hk)
  have hinv := htail.inv₀ hL
  have hquot := hrot.mul hinv
  have hbase :
      Tendsto (etaPairBaseRotation s) atTop (nhds (C * L⁻¹)) := by
    refine hquot.congr' ?_
    filter_upwards [htailNe] with k hk
    rw [etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul,
      mul_assoc, mul_inv_cancel₀ hk, mul_one]
  exact not_tendsto_etaPairBaseRotation_of_im_ne_zero him hbase

/-- Right-side normalization uses the dominant mirror exponent. -/
noncomputable def etaCriticalMirrorRightIndexNormalizedDefectTail
    (s : ℂ) (k : ℕ) : ℂ :=
  etaCriticalMirrorIndexNormalizedDefectTail (criticalMirror s).re s k

/-- Left-side normalization uses the dominant original exponent. -/
noncomputable def etaCriticalMirrorLeftIndexNormalizedDefectTail
    (s : ℂ) (k : ℕ) : ℂ :=
  etaCriticalMirrorIndexNormalizedDefectTail s.re s k

/-- Right of the critical line, the normalized unrotated defect tail has no fixed limit. -/
theorem not_tendsto_etaCriticalMirrorRightIndexNormalizedDefectTail
    {s L : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ Tendsto
      (etaCriticalMirrorRightIndexNormalizedDefectTail s)
      atTop (nhds L) := by
  have hrot :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail
          (criticalMirror s).re s)
        atTop
        (nhds (etaPairIndexNormalizedTailConstant (criticalMirror s))) := by
    simpa [etaCriticalMirrorIndexNormalizedRotatedDefectTail] using
      etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant
        hs hre
  simpa [etaCriticalMirrorRightIndexNormalizedDefectTail] using
    not_tendsto_etaCriticalMirrorIndexNormalizedDefectTail_of_rotated_limit
      (s := s) (L := L) him hrot
      (etaPairIndexNormalizedTailConstant_ne_zero (criticalMirror s))

/-- Left of the critical line, the normalized unrotated defect tail has no fixed limit. -/
theorem not_tendsto_etaCriticalMirrorLeftIndexNormalizedDefectTail
    {s L : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ Tendsto
      (etaCriticalMirrorLeftIndexNormalizedDefectTail s)
      atTop (nhds L) := by
  have hrot :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail s.re s)
        atTop
        (nhds (-etaPairIndexNormalizedTailConstant s)) := by
    simpa [etaCriticalMirrorIndexNormalizedRotatedDefectTail] using
      etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant
        hs hre
  simpa [etaCriticalMirrorLeftIndexNormalizedDefectTail] using
    not_tendsto_etaCriticalMirrorIndexNormalizedDefectTail_of_rotated_limit
      (s := s) (L := L) him hrot
      (neg_ne_zero.mpr (etaPairIndexNormalizedTailConstant_ne_zero s))

/-- The right normalized unrotated defect tail has no fixed complex limit. -/
theorem not_exists_etaCriticalMirrorRightIndexNormalizedDefectTail_limit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ ∃ L : ℂ,
      Tendsto
        (etaCriticalMirrorRightIndexNormalizedDefectTail s)
        atTop (nhds L) := by
  rintro ⟨L, hL⟩
  exact
    not_tendsto_etaCriticalMirrorRightIndexNormalizedDefectTail
      hs him hre hL

/-- The left normalized unrotated defect tail has no fixed complex limit. -/
theorem not_exists_etaCriticalMirrorLeftIndexNormalizedDefectTail_limit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ ∃ L : ℂ,
      Tendsto
        (etaCriticalMirrorLeftIndexNormalizedDefectTail s)
        atTop (nhds L) := by
  rintro ⟨L, hL⟩
  exact
    not_tendsto_etaCriticalMirrorLeftIndexNormalizedDefectTail
      hs him hre hL

/--
Off the critical line, the dominant index-normalized unrotated defect tail is
forced onto one of two nonconvergent branches.
-/
theorem etaCriticalMirrorOffCriticalNormalizedDefectTail_no_fixed_limit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    (s.re < (1 : ℝ) / 2 ∧
      ¬ ∃ L : ℂ,
        Tendsto
          (etaCriticalMirrorLeftIndexNormalizedDefectTail s)
          atTop (nhds L)) ∨
    ((1 : ℝ) / 2 < s.re ∧
      ¬ ∃ L : ℂ,
        Tendsto
          (etaCriticalMirrorRightIndexNormalizedDefectTail s)
          atTop (nhds L)) := by
  rcases lt_or_gt_of_ne hre with hleft | hright
  · exact Or.inl
      ⟨hleft,
        not_exists_etaCriticalMirrorLeftIndexNormalizedDefectTail_limit
          hs him hleft⟩
  · exact Or.inr
      ⟨hright,
        not_exists_etaCriticalMirrorRightIndexNormalizedDefectTail_limit
          hs him hright⟩

/-- Named certificate for the off-critical normalized-tail obstruction. -/
structure EtaCriticalMirrorOffCriticalNormalizedDefectTailFixedLimitObstructionCertificate
    (s : ℂ) : Prop where
  side_obstruction :
    (s.re < (1 : ℝ) / 2 ∧
      ¬ ∃ L : ℂ,
        Tendsto
          (etaCriticalMirrorLeftIndexNormalizedDefectTail s)
          atTop (nhds L)) ∨
    ((1 : ℝ) / 2 < s.re ∧
      ¬ ∃ L : ℂ,
        Tendsto
          (etaCriticalMirrorRightIndexNormalizedDefectTail s)
          atTop (nhds L))

/-- Every nonreal off-critical nontrivial zero carries the normalized-tail certificate. -/
theorem etaCriticalMirrorOffCriticalNormalizedDefectTailFixedLimitObstructionCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    EtaCriticalMirrorOffCriticalNormalizedDefectTailFixedLimitObstructionCertificate s :=
  ⟨etaCriticalMirrorOffCriticalNormalizedDefectTail_no_fixed_limit
    hs him hre⟩

end DkMath.RH.CFBRCProjection
