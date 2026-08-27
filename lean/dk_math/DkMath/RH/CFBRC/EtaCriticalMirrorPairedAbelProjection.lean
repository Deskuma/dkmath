/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairTermEventualSign
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjection"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Signed vertical projection of one defect pair in its pair-left frame. -/
noncomputable def etaCriticalMirrorRotatedDefectPairProjection
    (s : ℂ) (k : ℕ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorRotatedDefectPairTerm s k)

/-- Signed vertical projection of the moving-frame paired partial sum. -/
noncomputable def etaCriticalMirrorRotatedDefectProjectionPartial
    (K : ℕ) (s : ℂ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorRotatedDefectPairedPartial K s)

/-- The projected moving-frame partial sum gains exactly the next projected pair. -/
theorem etaCriticalMirrorRotatedDefectProjectionPartial_succ
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorRotatedDefectProjectionPartial (K + 1) s =
      etaCriticalMirrorRotatedDefectProjectionPartial K s +
        etaCriticalMirrorRotatedDefectPairProjection s K := by
  simp [etaCriticalMirrorRotatedDefectProjectionPartial,
    etaCriticalMirrorRotatedDefectPairProjection,
    etaCriticalMirrorRotatedDefectPairedPartial,
    etaCriticalMirrorSignedVerticalProjection,
    Finset.sum_range_succ, mul_add]

/-- The critical mirror of a nontrivial zeta zero is also nonzero. -/
private theorem criticalMirror_ne_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    criticalMirror s ≠ 0 := by
  intro hm0
  have hpos := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  simp [hm0] at hpos

/--
Right of the critical line, the projected moving-frame partial sums are
strictly increasing from some pair onward.
-/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_succ_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial K s <
        etaCriticalMirrorRotatedDefectProjectionPartial (K + 1) s := by
  have hterm :=
    eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_pos
      (nontrivialRiemannZetaZero_ne_zero hs)
      (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero hs)
      him hre
  filter_upwards [hterm] with K hK
  have hK' :
      0 < etaCriticalMirrorRotatedDefectPairProjection s K := by
    simpa [etaCriticalMirrorRotatedDefectPairProjection,
      etaCriticalMirrorRotatedDefectPairTerm] using hK
  rw [etaCriticalMirrorRotatedDefectProjectionPartial_succ]
  linarith

/--
Left of the critical line, the projected moving-frame partial sums are
strictly decreasing from some pair onward.
-/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionPartial_succ_lt_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial (K + 1) s <
        etaCriticalMirrorRotatedDefectProjectionPartial K s := by
  have hterm :=
    eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_neg
      (nontrivialRiemannZetaZero_ne_zero hs)
      (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero hs)
      him hre
  filter_upwards [hterm] with K hK
  have hK' :
      etaCriticalMirrorRotatedDefectPairProjection s K < 0 := by
    simpa [etaCriticalMirrorRotatedDefectPairProjection,
      etaCriticalMirrorRotatedDefectPairTerm] using hK
  rw [etaCriticalMirrorRotatedDefectProjectionPartial_succ]
  linarith

/--
The projected moving-frame partial sums converge to the signed vertical
projection of the exact negative Abel-correction `tsum`.
-/
theorem etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_neg_correction_projection
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorRotatedDefectProjectionPartial K s)
      atTop
      (nhds
        (etaCriticalMirrorSignedVerticalProjection s
          (-(∑' k : ℕ,
            etaCriticalMirrorPairedFrameCorrectionTerm s k)))) := by
  have hcomplex :=
    etaCriticalMirrorRotatedDefectPairedPartial_tendsto_neg_correction_tsum
      hs him
  have hcontinuous :
      Continuous (etaCriticalMirrorSignedVerticalProjection s) := by
    unfold etaCriticalMirrorSignedVerticalProjection
    fun_prop
  simpa [etaCriticalMirrorRotatedDefectProjectionPartial, Function.comp_def] using
    hcontinuous.continuousAt.tendsto.comp hcomplex

end DkMath.RH.CFBRCProjection
