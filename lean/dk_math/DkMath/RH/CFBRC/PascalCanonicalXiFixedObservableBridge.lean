/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
import DkMath.RH.CFBRC.CompletedZetaBridge
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge"

/-!
# Canonical entire centered Xi fixed observable

`pascalRiemannXiKernel` is a fixed entire function: unlike the PPW-017
mirror-frozen weights, it has no zero parameter.  This module deliberately
does not identify its fixed-observable contour theory with the frozen radial
mass; that requires later argument-principle and multiplicity-transport work.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Entire pole-killed completed-zeta kernel used as the fixed PPW observable. -/
noncomputable def pascalRiemannXiKernel (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1

theorem differentiable_pascalRiemannXiKernel :
    Differentiable ℂ pascalRiemannXiKernel := by
  unfold pascalRiemannXiKernel
  exact
    ((differentiable_id.mul
      ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)).mul
      differentiable_completedZeta₀).sub (differentiable_const (c := (1 : ℂ)))

@[simp] theorem pascalRiemannXiKernel_one_sub
    (s : ℂ) :
    pascalRiemannXiKernel (1 - s) = pascalRiemannXiKernel s := by
  unfold pascalRiemannXiKernel
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem ne_zero_of_pos_re
    {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hre0 : s.re = 0 := by simpa using hre
  exact hs.ne' hre0

theorem ne_one_of_re_lt_one
    {s : ℂ} (hs : s.re < 1) : s ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have hre1 : s.re = 1 := by simpa using hre
  exact hs.ne hre1

theorem gammaR_ne_zero_of_pos_re
    {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℝ s ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  have hre := congrArg Complex.re hn
  norm_num at hre
  have hnonpos : s.re ≤ 0 := by
    rw [hre]
    exact neg_nonpos.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
  linarith

theorem pascalRiemannXiKernel_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    pascalRiemannXiKernel s =
      s * (1 - s) * completedRiemannZeta s := by
  have hsub : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold pascalRiemannXiKernel
  rw [completedRiemannZeta_eq]
  field_simp
  ring

theorem pascalRiemannXiKernel_eq_zero_iff_completedRiemannZeta_eq_zero_of_openCriticalStrip
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    pascalRiemannXiKernel s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [pascalRiemannXiKernel_eq_mul_completedRiemannZeta
    (ne_zero_of_pos_re hs0) (ne_one_of_re_lt_one hs1)]
  have hfactor : s * (1 - s) ≠ 0 :=
    mul_ne_zero (ne_zero_of_pos_re hs0)
      (sub_ne_zero.mpr (Ne.symm (ne_one_of_re_lt_one hs1)))
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact False.elim (hfactor h)
    · exact h
  · intro h
    exact mul_eq_zero_of_right _ h

theorem pascalRiemannXiKernel_eq_zero_iff_riemannZeta_eq_zero_of_openCriticalStrip
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    pascalRiemannXiKernel s = 0 ↔ riemannZeta s = 0 := by
  rw [pascalRiemannXiKernel_eq_zero_iff_completedRiemannZeta_eq_zero_of_openCriticalStrip
    hs0 hs1,
    ← riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
      (ne_zero_of_pos_re hs0) (gammaR_ne_zero_of_pos_re hs0)]

theorem pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    pascalRiemannXiKernel s = 0 := by
  exact
    (pascalRiemannXiKernel_eq_zero_iff_riemannZeta_eq_zero_of_openCriticalStrip
      (nontrivialRiemannZetaZero_mem_openCriticalStrip hs).1
      (nontrivialRiemannZetaZero_mem_openCriticalStrip hs).2).mpr hs.1

/-- The fixed entire Xi kernel, expressed in the coordinate centered at `1 / 2`. -/
noncomputable def pascalCenteredRiemannXiKernel (z : ℂ) : ℂ :=
  pascalRiemannXiKernel (criticalLineCenter + z)

theorem differentiable_pascalCenteredRiemannXiKernel :
    Differentiable ℂ pascalCenteredRiemannXiKernel := by
  unfold pascalCenteredRiemannXiKernel
  exact differentiable_pascalRiemannXiKernel.comp
    ((differentiable_const (c := criticalLineCenter)).add differentiable_id)

@[simp] theorem pascalCenteredRiemannXiKernel_neg
    (z : ℂ) :
    pascalCenteredRiemannXiKernel (-z) =
      pascalCenteredRiemannXiKernel z := by
  unfold pascalCenteredRiemannXiKernel
  rw [show criticalLineCenter + -z = 1 - (criticalLineCenter + z) by
    apply Complex.ext
    · simp [criticalLineCenter]
      ring
    · simp [criticalLineCenter]]
  exact pascalRiemannXiKernel_one_sub _

theorem pascalCenteredRiemannXiKernel_sub_center_eq_zero_of_nontrivial
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    pascalCenteredRiemannXiKernel (s - criticalLineCenter) = 0 := by
  unfold pascalCenteredRiemannXiKernel
  have harg : criticalLineCenter + (s - criticalLineCenter) = s := by ring
  rw [harg]
  exact pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero hs

/-- A zero-independent fixed log-derivative candidate for later outer-contour work. -/
noncomputable def pascalCenteredXiNegLogDeriv (z : ℂ) : ℂ :=
  -logDeriv pascalCenteredRiemannXiKernel z

end DkMath.RH.CFBRCProjection
