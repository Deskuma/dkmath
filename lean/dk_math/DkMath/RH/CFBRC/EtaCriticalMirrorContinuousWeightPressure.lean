/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightPressure"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Right of the critical line, the continuous transport weight expands for every `x > 1`. -/
theorem one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    1 < etaCriticalMirrorContinuousWeightR s x := by
  unfold etaCriticalMirrorContinuousWeightR
  apply Real.one_lt_rpow hx
  have hcenter : 0 < centeredSigma s.re := by
    unfold centeredSigma
    linarith
  positivity

/-- Left of the critical line, the continuous transport weight contracts for every `x > 1`. -/
theorem etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorContinuousWeightR s x < 1 := by
  unfold etaCriticalMirrorContinuousWeightR
  apply Real.rpow_lt_one_of_one_lt_of_neg hx
  have hcenter : centeredSigma s.re < 0 := by
    unfold centeredSigma
    linarith
  nlinarith

/-- On the critical line, the continuous transport weight is exactly one. -/
theorem etaCriticalMirrorContinuousWeightR_eq_one_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (x : ℝ) :
    etaCriticalMirrorContinuousWeightR s x = 1 := by
  have hcenter : centeredSigma s.re = 0 :=
    (centeredSigma_eq_zero_iff s.re).2 hre
  simp [etaCriticalMirrorContinuousWeightR, hcenter]

/-- For every `x > 1`, unit continuous transport is equivalent to the critical line. -/
theorem etaCriticalMirrorContinuousWeightR_eq_one_iff_re_eq_half
    (s : ℂ) {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorContinuousWeightR s x = 1 ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hunit
    rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
    · have hlt :=
        etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hleft hx
      linarith
    · exact hline
    · have hgt :=
        one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hright hx
      linarith
  · intro hre
    exact etaCriticalMirrorContinuousWeightR_eq_one_of_re_eq_half hre x

/-- Complete left/center/right classification of the continuous transport weight. -/
theorem etaCriticalMirrorContinuousWeightR_pressure_trichotomy
    (s : ℂ) {x : ℝ} (hx : 1 < x) :
    (s.re < (1 : ℝ) / 2 ∧ etaCriticalMirrorContinuousWeightR s x < 1) ∨
    (s.re = (1 : ℝ) / 2 ∧ etaCriticalMirrorContinuousWeightR s x = 1) ∨
    ((1 : ℝ) / 2 < s.re ∧ 1 < etaCriticalMirrorContinuousWeightR s x) := by
  rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
  · exact Or.inl ⟨hleft,
      etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hleft hx⟩
  · exact Or.inr <| Or.inl ⟨hline,
      etaCriticalMirrorContinuousWeightR_eq_one_of_re_eq_half hline x⟩
  · exact Or.inr <| Or.inr ⟨hright,
      one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hright hx⟩

/-- Above the real axis and right of the critical line, the coefficient points upward. -/
theorem etaCriticalMirrorDefectCoefficient_im_pos_of_im_pos_of_half_lt_re
    {s : ℂ} (him : 0 < s.im) (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    0 < (etaCriticalMirrorDefectCoefficient s x).im := by
  rw [etaCriticalMirrorDefectCoefficient_im s (lt_trans zero_lt_one hx)]
  exact mul_pos him
    (sub_pos.mpr
      (one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hre hx))

/-- Above the real axis and left of the critical line, the coefficient points downward. -/
theorem etaCriticalMirrorDefectCoefficient_im_neg_of_im_pos_of_re_lt_half
    {s : ℂ} (him : 0 < s.im) (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    (etaCriticalMirrorDefectCoefficient s x).im < 0 := by
  rw [etaCriticalMirrorDefectCoefficient_im s (lt_trans zero_lt_one hx)]
  exact mul_neg_of_pos_of_neg him
    (sub_neg.mpr
      (etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hre hx))

/-- Below the real axis and right of the critical line, the coefficient points downward. -/
theorem etaCriticalMirrorDefectCoefficient_im_neg_of_im_neg_of_half_lt_re
    {s : ℂ} (him : s.im < 0) (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    (etaCriticalMirrorDefectCoefficient s x).im < 0 := by
  rw [etaCriticalMirrorDefectCoefficient_im s (lt_trans zero_lt_one hx)]
  exact mul_neg_of_neg_of_pos him
    (sub_pos.mpr
      (one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hre hx))

/-- Below the real axis and left of the critical line, the coefficient points upward. -/
theorem etaCriticalMirrorDefectCoefficient_im_pos_of_im_neg_of_re_lt_half
    {s : ℂ} (him : s.im < 0) (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    0 < (etaCriticalMirrorDefectCoefficient s x).im := by
  rw [etaCriticalMirrorDefectCoefficient_im s (lt_trans zero_lt_one hx)]
  exact mul_pos_of_neg_of_neg him
    (sub_neg.mpr
      (etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hre hx))

/-- A nonreal off-critical point has a nonzero continuous defect coefficient at every `x > 1`. -/
theorem etaCriticalMirrorDefectCoefficient_ne_zero_of_im_ne_zero_of_re_ne_half
    {s : ℂ} (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorDefectCoefficient s x ≠ 0 := by
  have hweight : etaCriticalMirrorContinuousWeightR s x ≠ 1 := by
    exact mt
      (etaCriticalMirrorContinuousWeightR_eq_one_iff_re_eq_half s hx).mp
      hre
  have himCoeff : (etaCriticalMirrorDefectCoefficient s x).im ≠ 0 := by
    rw [etaCriticalMirrorDefectCoefficient_im s (lt_trans zero_lt_one hx)]
    exact mul_ne_zero him (sub_ne_zero.mpr hweight)
  intro hzero
  apply himCoeff
  simpa [hzero]

end DkMath.RH.CFBRCProjection
