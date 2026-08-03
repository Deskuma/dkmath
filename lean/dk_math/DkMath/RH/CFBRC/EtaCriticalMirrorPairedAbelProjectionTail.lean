/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimitSide
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjectionTail"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Infinite signed projection tail beginning at pair index `K`. -/
noncomputable def etaCriticalMirrorRotatedDefectProjectionTail
    (K : ℕ) (s : ℂ) : ℝ :=
  ∑' n : ℕ,
    etaCriticalMirrorRotatedDefectPairProjection s (n + K)

/--
The pair-left rotated defect projections form a summable real series at every
nontrivial zeta zero.

The varying rotations have unit norm.  The signed vertical projection is
therefore bounded by `|s.im|` times the already summable paired-defect
majorant.
-/
theorem summable_etaCriticalMirrorRotatedDefectPairProjection
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Summable
      (fun k : ℕ =>
        etaCriticalMirrorRotatedDefectPairProjection s k) := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hmajorant :
      Summable
        (fun k : ℕ =>
          |s.im| * etaCriticalMirrorDefectPairMajorant s k) :=
    (summable_etaCriticalMirrorDefectPairMajorant hsre hmre).mul_left |s.im|
  refine Summable.of_norm_bounded hmajorant ?_
  intro k
  rw [Real.norm_eq_abs]
  unfold etaCriticalMirrorRotatedDefectPairProjection
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [abs_mul]
  calc
    |s.im| * |(etaCriticalMirrorRotatedDefectPairTerm s k).im| ≤
        |s.im| * ‖etaCriticalMirrorRotatedDefectPairTerm s k‖ :=
      mul_le_mul_of_nonneg_left
        (Complex.abs_im_le_norm
          (etaCriticalMirrorRotatedDefectPairTerm s k))
        (abs_nonneg s.im)
    _ = |s.im| * ‖etaCriticalMirrorDefectPairTerm s k‖ := by
      rw [etaCriticalMirrorRotatedDefectPairTerm, norm_mul,
        norm_etaPairBaseRotation, one_mul]
    _ ≤ |s.im| * etaCriticalMirrorDefectPairMajorant s k :=
      mul_le_mul_of_nonneg_left
        (norm_etaCriticalMirrorDefectPairTerm_le_majorant hsre hmre k)
        (abs_nonneg s.im)

/-- The named projection tail is summable after every finite prefix. -/
theorem summable_etaCriticalMirrorRotatedDefectProjectionTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (K : ℕ) :
    Summable
      (fun n : ℕ =>
        etaCriticalMirrorRotatedDefectPairProjection s (n + K)) :=
  (summable_nat_add_iff K).2
    (summable_etaCriticalMirrorRotatedDefectPairProjection hs)

/--
The moving-frame projected partial is exactly the finite sum of its projected
pair terms.
-/
theorem etaCriticalMirrorRotatedDefectProjectionPartial_eq_sum_range
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorRotatedDefectProjectionPartial K s =
      (Finset.range K).sum
        (etaCriticalMirrorRotatedDefectPairProjection s) := by
  simp [etaCriticalMirrorRotatedDefectProjectionPartial,
    etaCriticalMirrorRotatedDefectPairProjection,
    etaCriticalMirrorRotatedDefectPairedPartial,
    etaCriticalMirrorSignedVerticalProjection,
    Finset.mul_sum]

/--
The complete projected pair `tsum` is the named Abel-limit coordinate.

Both are limits of the same finite projected partial sequence, so no direct
exchange between the complex correction `tsum` and the real projection is
needed.
-/
theorem tsum_etaCriticalMirrorRotatedDefectPairProjection_eq_limit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    (∑' k : ℕ,
      etaCriticalMirrorRotatedDefectPairProjection s k) =
      etaCriticalMirrorRotatedDefectProjectionLimit s := by
  have hsum :=
    summable_etaCriticalMirrorRotatedDefectPairProjection hs
  have htsum :
      Tendsto
        (fun K : ℕ =>
          etaCriticalMirrorRotatedDefectProjectionPartial K s)
        atTop
        (nhds
          (∑' k : ℕ,
            etaCriticalMirrorRotatedDefectPairProjection s k)) := by
    simpa only
      [etaCriticalMirrorRotatedDefectProjectionPartial_eq_sum_range] using
      hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique htsum
    (etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_limit hs him)

/--
The signed gap from a projected partial sum to its Abel limit is exactly the
infinite tail of the actual projected pair series.
-/
theorem etaCriticalMirrorRotatedDefectProjectionLimitGap_eq_tsum_nat_add
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaCriticalMirrorRotatedDefectProjectionLimitGap K s =
      etaCriticalMirrorRotatedDefectProjectionTail K s := by
  have hsum :=
    summable_etaCriticalMirrorRotatedDefectPairProjection hs
  have hsplit := hsum.sum_add_tsum_nat_add K
  rw [etaCriticalMirrorRotatedDefectProjectionLimitGap,
    ← tsum_etaCriticalMirrorRotatedDefectPairProjection_eq_limit hs him,
    etaCriticalMirrorRotatedDefectProjectionPartial_eq_sum_range]
  unfold etaCriticalMirrorRotatedDefectProjectionTail
  linear_combination hsplit

/-- Right of the critical line, every sufficiently late actual projection tail is positive. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionTail_pos_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorRotatedDefectProjectionTail K s := by
  filter_upwards
    [eventually_etaCriticalMirrorRotatedDefectProjectionLimitGap_pos_of_half_lt_re
      hs him hre] with K hK
  rwa [etaCriticalMirrorRotatedDefectProjectionLimitGap_eq_tsum_nat_add
    hs him K] at hK

/-- Left of the critical line, every sufficiently late actual projection tail is negative. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionTail_neg_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionTail K s < 0 := by
  filter_upwards
    [eventually_etaCriticalMirrorRotatedDefectProjectionLimitGap_neg_of_re_lt_half
      hs him hre] with K hK
  rwa [etaCriticalMirrorRotatedDefectProjectionLimitGap_eq_tsum_nat_add
    hs him K] at hK

end DkMath.RH.CFBRCProjection
