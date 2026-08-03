/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightPressure
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientProjection"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/--
Signed projection onto the vertical direction determined by `s`.

Multiplying the imaginary coordinate by `s.im` removes the distinction between
the upper and lower half-planes.  Positive and negative values can therefore
encode only the right/left pressure relative to the critical line.
-/
def etaCriticalMirrorSignedVerticalProjection
    (s z : ℂ) : ℝ :=
  s.im * z.im

/--
The signed vertical projection of the continuous defect coefficient is exactly
`s.im²` times the transport-weight displacement from one.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) =
      s.im ^ 2 *
        (etaCriticalMirrorContinuousWeightR s x - 1) := by
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [etaCriticalMirrorDefectCoefficient_im s hx]
  ring

/--
At a nonreal point right of the critical line, the signed vertical projection
of the defect coefficient is strictly positive for every `x > 1`.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_pos_of_half_lt_re
    {s : ℂ} (him : s.im ≠ 0)
    (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    0 <
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq
    s (lt_trans zero_lt_one hx)]
  exact mul_pos
    (sq_pos_of_ne_zero him)
    (sub_pos.mpr
      (one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hre hx))

/--
At a nonreal point left of the critical line, the signed vertical projection
of the defect coefficient is strictly negative for every `x > 1`.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_neg_of_re_lt_half
    {s : ℂ} (him : s.im ≠ 0)
    (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) < 0 := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq
    s (lt_trans zero_lt_one hx)]
  exact mul_neg_of_pos_of_neg
    (sq_pos_of_ne_zero him)
    (sub_neg.mpr
      (etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hre hx))

/-- On the critical line, the signed vertical projection vanishes. -/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq_zero_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) = 0 := by
  rw [etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq s hx]
  rw [etaCriticalMirrorContinuousWeightR_eq_one_of_re_eq_half hre x]
  ring

/--
Complete left/center/right sign classification of the signed vertical defect
coefficient projection at every informative positive-real point `x > 1`.
-/
theorem etaCriticalMirrorSignedVerticalProjection_defectCoefficient_sign_trichotomy
    (s : ℂ) (him : s.im ≠ 0)
    {x : ℝ} (hx : 1 < x) :
    (s.re < (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) < 0) ∨
    (s.re = (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) = 0) ∨
    ((1 : ℝ) / 2 < s.re ∧
      0 < etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)) := by
  rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
  · exact Or.inl ⟨hleft,
      etaCriticalMirrorSignedVerticalProjection_defectCoefficient_neg_of_re_lt_half
        him hleft hx⟩
  · exact Or.inr <| Or.inl ⟨hline,
      etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq_zero_of_re_eq_half
        hline (lt_trans zero_lt_one hx)⟩
  · exact Or.inr <| Or.inr ⟨hright,
      etaCriticalMirrorSignedVerticalProjection_defectCoefficient_pos_of_half_lt_re
        him hright hx⟩

end DkMath.RH.CFBRCProjection
