/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- Multiplying a shifted real power by the reciprocal base adds one decay power. -/
theorem one_div_nat_succ_mul_rpow_neg_eq
    (σ : ℝ) (k : ℕ) :
    (1 / (((k + 1 : ℕ) : ℝ))) *
        (((k + 1 : ℕ) : ℝ) ^ (-σ)) =
      (((k + 1 : ℕ) : ℝ) ^ (-σ - 1)) := by
  have hx : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  rw [one_div, ← Real.rpow_neg_one]
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- Summable p-series majorant for the moving-frame Abel correction. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionMajorant
    (s : ℂ) (k : ℕ) : ℝ :=
  (4 * |s.im| / (criticalMirror s).re) *
      (‖criticalMirror s‖ *
        (((k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 1))) +
    (4 * |s.im| / s.re) *
      (‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)))

/-- The Abel-correction majorant is summable throughout the open mirror strip. -/
theorem summable_etaCriticalMirrorPairedFrameCorrectionMajorant
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorPairedFrameCorrectionMajorant s) := by
  unfold etaCriticalMirrorPairedFrameCorrectionMajorant
  exact
    ((summable_etaPairMajorant hm).mul_left
      (4 * |s.im| / (criticalMirror s).re)).add
      ((summable_etaPairMajorant hs).mul_left
        (4 * |s.im| / s.re))

/-- The reciprocal pair-left endpoint is bounded by the reciprocal successor index. -/
theorem abs_im_div_etaPairFrameLeftEndpoint_le_succ
    (s : ℂ) (k : ℕ) :
    |s.im| / etaPairFrameLeftEndpoint k ≤
      |s.im| / (((k + 1 : ℕ) : ℝ)) := by
  have hleft : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hsucc : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have horder :
      (((k + 1 : ℕ) : ℝ)) ≤ etaPairFrameLeftEndpoint k := by
    unfold etaPairFrameLeftEndpoint
    exact_mod_cast (by omega : k + 1 ≤ 2 * k + 1)
  exact
    (div_le_div_iff₀ hleft hsucc).2
      (mul_le_mul_of_nonneg_left horder (abs_nonneg s.im))

/--
One moving-frame Abel correction is bounded by a summable p-series majorant.
The proof combines the shrinking frame chord with the exact defect-tail
representation at a nonreal nontrivial zero.
-/
theorem norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (k : ℕ) (hspan : etaPairFrameStepSpan s k ≤ 1) :
    ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
      etaCriticalMirrorPairedFrameCorrectionMajorant s k := by
  have hsre : 0 < s.re := nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hpartial :
      ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ ≤
        ‖criticalMirror s‖ *
            (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
              (criticalMirror s).re) +
          ‖s‖ *
            (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re) := by
    rw [etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him (k + 1), norm_neg]
    exact norm_etaCriticalMirrorDefectPairTail_le hsre hmre (by omega)
  have hframe := etaPairFrameStepSpan_le_two_mul_inv s k
  have hrecip := abs_im_div_etaPairFrameLeftEndpoint_le_succ s k
  have hleft : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hcoefficientNonneg :
      0 ≤ 2 * (2 * (|s.im| / etaPairFrameLeftEndpoint k)) := by
    positivity
  have htailNonneg :
      0 ≤
        ‖criticalMirror s‖ *
            (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
              (criticalMirror s).re) +
          ‖s‖ *
            (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re) := by
    positivity
  have hcoefficient :
      2 * (2 * (|s.im| / etaPairFrameLeftEndpoint k)) ≤
        4 * (|s.im| / (((k + 1 : ℕ) : ℝ))) := by
    nlinarith [hrecip]
  calc
    ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
        2 * etaPairFrameStepSpan s k *
          ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ :=
      norm_etaCriticalMirrorPairedFrameCorrectionTerm_le s k hspan
    _ ≤
        2 * (2 * (|s.im| / etaPairFrameLeftEndpoint k)) *
          ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ := by
      gcongr
    _ ≤
        2 * (2 * (|s.im| / etaPairFrameLeftEndpoint k)) *
          (‖criticalMirror s‖ *
              (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
                (criticalMirror s).re) +
            ‖s‖ *
              (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re)) := by
      exact mul_le_mul_of_nonneg_left hpartial hcoefficientNonneg
    _ ≤
        4 * (|s.im| / (((k + 1 : ℕ) : ℝ))) *
          (‖criticalMirror s‖ *
              (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
                (criticalMirror s).re) +
            ‖s‖ *
              (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re)) := by
      exact mul_le_mul_of_nonneg_right hcoefficient htailNonneg
    _ = etaCriticalMirrorPairedFrameCorrectionMajorant s k := by
      have hpowMirror :=
        one_div_nat_succ_mul_rpow_neg_eq (criticalMirror s).re k
      have hpowOriginal := one_div_nat_succ_mul_rpow_neg_eq s.re k
      unfold etaCriticalMirrorPairedFrameCorrectionMajorant
      rw [← hpowMirror, ← hpowOriginal]
      simp only [div_eq_mul_inv]
      ring

/-- Eventually every Abel correction is bounded by the summable majorant. -/
theorem eventually_norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
        etaCriticalMirrorPairedFrameCorrectionMajorant s k := by
  filter_upwards
    [(etaPairFrameStepSpan_tendsto_zero s).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)] with k hk
  exact
    norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
      hs him k hk.le

/-- The moving-frame Abel correction series is summable at every nonreal nontrivial zero. -/
theorem summable_etaCriticalMirrorPairedFrameCorrectionTerm_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Summable (etaCriticalMirrorPairedFrameCorrectionTerm s) := by
  exact
    Summable.of_norm_bounded_eventually_nat
      (summable_etaCriticalMirrorPairedFrameCorrectionMajorant
        (nontrivialRiemannZetaZero_re_pos hs)
        (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs))
      (eventually_norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
        hs him)

end DkMath.RH.CFBRCProjection
