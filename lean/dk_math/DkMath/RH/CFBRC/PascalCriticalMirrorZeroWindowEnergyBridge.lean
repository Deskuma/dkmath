/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalZetaLogDerivativeZeroBridge
import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import DkMath.RH.CFBRC.PrimeMirrorOffsetCore
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter

theorem nontrivialRiemannZetaZero_mem_riemannZetaZeros
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) : s ∈ riemannZetaZeros :=
  mem_riemannZetaZeros.mpr hs.1

noncomputable def criticalLineCenter : ℂ := (1 : ℂ) / 2

theorem dist_criticalMirror_criticalLineCenter (s : ℂ) :
    dist (criticalMirror s) criticalLineCenter = dist s criticalLineCenter := by
  rw [Complex.dist_eq, Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq,
    Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp [criticalMirror, criticalLineCenter]
  ring

@[simp] theorem criticalMirror_mem_closedBall_iff {R : ℝ} {s : ℂ} :
    criticalMirror s ∈ Metric.closedBall criticalLineCenter R ↔
      s ∈ Metric.closedBall criticalLineCenter R := by
  simp only [Metric.mem_closedBall, dist_criticalMirror_criticalLineCenter]

noncomputable def pascalCriticalMirrorZeroWindow (R : ℝ) : Set ℂ :=
  {s | s ∈ Metric.closedBall criticalLineCenter R ∧ NontrivialRiemannZetaZero s}

@[simp] theorem mem_pascalCriticalMirrorZeroWindow_iff {R : ℝ} {s : ℂ} :
    s ∈ pascalCriticalMirrorZeroWindow R ↔
      s ∈ Metric.closedBall criticalLineCenter R ∧ NontrivialRiemannZetaZero s := Iff.rfl

theorem finite_pascalCriticalMirrorZeroWindow (R : ℝ) :
    (pascalCriticalMirrorZeroWindow R).Finite := by
  apply (finite_riemannZetaZeros_in_compact (isCompact_closedBall _ _)).subset
  · intro s hs
    exact ⟨hs.1, nontrivialRiemannZetaZero_mem_riemannZetaZeros hs.2⟩

noncomputable def pascalCriticalMirrorZeroWindowFinset (R : ℝ) : Finset ℂ :=
  (finite_pascalCriticalMirrorZeroWindow R).toFinset

@[simp] theorem mem_pascalCriticalMirrorZeroWindowFinset_iff {R : ℝ} {s : ℂ} :
    s ∈ pascalCriticalMirrorZeroWindowFinset R ↔ s ∈ pascalCriticalMirrorZeroWindow R := by
  simp [pascalCriticalMirrorZeroWindowFinset]

@[simp] theorem criticalMirror_mem_pascalCriticalMirrorZeroWindow_iff {R : ℝ} {s : ℂ} :
    criticalMirror s ∈ pascalCriticalMirrorZeroWindow R ↔ s ∈ pascalCriticalMirrorZeroWindow R := by
  constructor
  · intro hs
    refine ⟨criticalMirror_mem_closedBall_iff.mp hs.1, ?_⟩
    simpa only [criticalMirror_involutive] using
      criticalMirror_nontrivialRiemannZetaZero hs.2
  · rintro ⟨hsball, hszero⟩
    exact ⟨criticalMirror_mem_closedBall_iff.mpr hsball,
      criticalMirror_nontrivialRiemannZetaZero hszero⟩

theorem image_criticalMirror_pascalCriticalMirrorZeroWindowFinset (R : ℝ) :
    (pascalCriticalMirrorZeroWindowFinset R).image criticalMirror =
      pascalCriticalMirrorZeroWindowFinset R := by
  ext s
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxs⟩
    rw [mem_pascalCriticalMirrorZeroWindowFinset_iff] at hx ⊢
    rw [← hxs]
    exact criticalMirror_mem_pascalCriticalMirrorZeroWindow_iff.mpr hx
  · intro hs
    rw [mem_pascalCriticalMirrorZeroWindowFinset_iff] at hs
    refine ⟨criticalMirror s, ?_, criticalMirror_involutive s⟩
    rw [mem_pascalCriticalMirrorZeroWindowFinset_iff]
    exact criticalMirror_mem_pascalCriticalMirrorZeroWindow_iff.mpr hs

noncomputable def pascalCriticalMirrorZeroWindowEnergy (n : ℕ) (R : ℝ) : ℝ :=
  (pascalCriticalMirrorZeroWindowFinset R).sum (primeMirrorOffsetGapAt n)

theorem pascalCriticalMirrorZeroWindowEnergy_nonneg (n : ℕ) (R : ℝ) :
    0 ≤ pascalCriticalMirrorZeroWindowEnergy n R := by
  exact Finset.sum_nonneg fun _ _ => primeMirrorOffsetGap_nonneg _ _

theorem pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowEnergy n R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R, ρ.re = (1 : ℝ) / 2 := by
  change (pascalCriticalMirrorZeroWindowFinset R).sum
      (primeMirrorOffsetGapAt n) = 0 ↔ _
  refine (Finset.sum_eq_zero_iff_of_nonneg
    (f := primeMirrorOffsetGapAt n) (s := pascalCriticalMirrorZeroWindowFinset R)
    (fun ρ _ => primeMirrorOffsetGap_nonneg n (centeredSigma ρ.re))).trans ?_
  simp_rw [primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half hn]

theorem tendsto_mul_pascalZetaNegLogDeriv_simpleZero_of_mem_window
    {R : ℝ} {ρ : ℂ} (hρ : ρ ∈ pascalCriticalMirrorZeroWindow R)
    (hρsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun w => (w - ρ) * pascalZetaNegLogDeriv w)
      (nhdsWithin ρ {ρ}ᶜ) (nhds (-1)) :=
  tendsto_mul_pascalZetaNegLogDeriv_simpleZero
    (nontrivialRiemannZetaZero_mem_riemannZetaZeros hρ.2) hρsimple

end DkMath.RH.CFBRCProjection
