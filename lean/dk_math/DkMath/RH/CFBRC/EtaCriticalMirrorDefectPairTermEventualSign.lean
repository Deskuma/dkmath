/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairTermEventualSign"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter MeasureTheory
open scoped Topology

/-- Every natural eta-pair interval has positive length. -/
private theorem etaPairFrameLeftEndpoint_lt_rightEndpoint
    (k : ℕ) :
    etaPairFrameLeftEndpoint k < etaPairFrameRightEndpoint k := by
  unfold etaPairFrameLeftEndpoint etaPairFrameRightEndpoint
  exact_mod_cast (by omega : 2 * k + 1 < 2 * k + 2)

/-- The pair-left rotated defect kernel is integrable on its natural interval. -/
private theorem etaPairBaseRotation_mul_defectPairIntegralKernel_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x)
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  have hleft : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hle :
      etaPairFrameLeftEndpoint k ≤ etaPairFrameRightEndpoint k :=
    (etaPairFrameLeftEndpoint_lt_rightEndpoint k).le
  exact
    (etaCriticalMirrorDefectPairIntegralKernel_intervalIntegrable
      s hleft hle).const_mul (etaPairBaseRotation s k)

/-- The signed vertical projection of the rotated defect kernel is integrable. -/
private theorem etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_intervalIntegrable
    (s : ℂ) (k : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x))
      volume
      (etaPairFrameLeftEndpoint k)
      (etaPairFrameRightEndpoint k) := by
  have hcomplex :=
    etaPairBaseRotation_mul_defectPairIntegralKernel_intervalIntegrable s k
  have him :
      IntervalIntegrable
        (fun x : ℝ =>
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x).im)
        volume
        (etaPairFrameLeftEndpoint k)
        (etaPairFrameRightEndpoint k) :=
    ⟨hcomplex.1.im, hcomplex.2.im⟩
  simpa [etaCriticalMirrorSignedVerticalProjection] using
    him.const_mul s.im

/-- Constant pair-frame rotation can be moved inside the defect-pair integral. -/
theorem etaPairBaseRotation_mul_defectPairTerm_eq_intervalIntegral
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ) :
    etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k =
      ∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        etaPairBaseRotation s k *
          etaCriticalMirrorDefectPairIntegralKernel s x := by
  rw [etaCriticalMirrorDefectPairTerm_eq_intervalIntegral hs hm k]
  change
    etaPairBaseRotation s k *
        (∫ x : ℝ in
            (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
          etaCriticalMirrorDefectPairIntegralKernel s x) = _
  rw [intervalIntegral.integral_const_mul]

/-- Signed vertical projection commutes with every integrable interval integral. -/
theorem etaCriticalMirrorSignedVerticalProjection_intervalIntegral
    (s : ℂ) {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b) :
    etaCriticalMirrorSignedVerticalProjection s
        (∫ x : ℝ in a..b, f x) =
      ∫ x : ℝ in a..b,
        etaCriticalMirrorSignedVerticalProjection s (f x) := by
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [intervalIntegral.integral_const_mul]
  simpa using
    congrArg (fun y : ℝ => s.im * y)
      (intervalIntegral.intervalIntegral_im hf).symm

/--
The signed projection of one rotated defect pair is exactly the interval
integral of the pointwise signed projection in the same pair frame.
-/
theorem etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_eq_intervalIntegral
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k) =
      ∫ x : ℝ in
          (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
        etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x) := by
  rw [etaPairBaseRotation_mul_defectPairTerm_eq_intervalIntegral hs hm k]
  exact
    etaCriticalMirrorSignedVerticalProjection_intervalIntegral s
      (etaPairBaseRotation_mul_defectPairIntegralKernel_intervalIntegrable s k)

/--
Right of the critical line, every sufficiently late rotated defect pair has
strictly positive signed vertical projection.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_pos
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      0 < etaCriticalMirrorSignedVerticalProjection s
        (etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k) := by
  filter_upwards
    [eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_pos_on_pair
      him hre] with k hk
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_eq_intervalIntegral
    hs hm k]
  exact
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_intervalIntegrable
        s k)
      (fun x hx => hk x hx.1.le hx.2.le)
      (etaPairFrameLeftEndpoint_lt_rightEndpoint k)

/--
Left of the critical line, every sufficiently late rotated defect pair has
strictly negative signed vertical projection.
-/
theorem eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_neg
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k) < 0 := by
  filter_upwards
    [eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_neg_on_pair
      him hre] with k hk
  rw [etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_eq_intervalIntegral
    hs hm k]
  have hpos :
      0 <
        ∫ x : ℝ in
            (etaPairFrameLeftEndpoint k)..(etaPairFrameRightEndpoint k),
          -etaCriticalMirrorSignedVerticalProjection s
            (etaPairBaseRotation s k *
              etaCriticalMirrorDefectPairIntegralKernel s x) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_intervalIntegrable
        s k).neg
      (fun x hx => neg_pos.mpr (hk x hx.1.le hx.2.le))
      (etaPairFrameLeftEndpoint_lt_rightEndpoint k)
  rw [intervalIntegral.integral_neg] at hpos
  linarith

end DkMath.RH.CFBRCProjection
