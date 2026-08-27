/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
import Mathlib.Tactic

/-!
# Safe-radius annulus and zero-window stability

This module implements the finite radial-gap route for a boundary-safe radius.
The centered Xi zeros in the slightly larger compact disk of radius `R + 1`
form a finite set; the positive minimum distance of their radial values from
`R`, together with `R / 2` and `1`, supplies a stable annulus.

The result is local constancy of the finite zero window.  It is not a smooth
spectral cutoff, a Mellin transform realization, a zero-free theorem for the
whole plane, or an RH/explicit-formula statement.  In particular, the hard
radial indicator remains a separate object on the spectral side.
-/

namespace DkMath.RH.CFBRCProjection

open Set

private theorem exists_pos_finset_abs_sub_lower_bound
    {R : ℝ} (S : Finset ℝ) (hR : R ∉ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ S, δ ≤ |d - R| := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      simp
  | @insert d S hd ih =>
      have hdR : d ≠ R := by
        intro h
        apply hR
        simp [h]
      have hSR : R ∉ S := by
        intro h
        apply hR
        simp [h]
      obtain ⟨δ, hδ, hδS⟩ := ih hSR
      refine ⟨min δ |d - R|, lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr hdR)), ?_⟩
      intro e he
      simp only [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hδS e he)

private theorem exists_safeRadius_radial_gap
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ pascalCenteredXiZeros,
        |dist z 0 - R| < ε → False) := by
  classical
  let S : Finset ℝ :=
    (pascalCenteredXiZeroDiskFinset (R + 1)).image (fun z : ℂ => dist z 0)
  have hRnot : R ∉ S := by
    intro hRmem
    rcases Finset.mem_image.mp hRmem with ⟨z, hz, hzr⟩
    have hzDisk := (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz)
    have hzSphere : z ∈ Metric.sphere (0 : ℂ) R :=
      Metric.mem_sphere.mpr hzr
    exact (hR.2 z hzSphere) (mem_pascalCenteredXiZeros.mp hzDisk.2)
  obtain ⟨δ, hδ, hδS⟩ := exists_pos_finset_abs_sub_lower_bound S hRnot
  let ε : ℝ := min δ (min 1 (R / 2))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ (lt_min zero_lt_one (half_pos hR.1))
  refine ⟨ε, hε, ?_⟩
  intro z hz hnear
  have hzdist_nonneg : 0 ≤ dist z 0 := dist_nonneg
  have hε_le_one : ε ≤ 1 :=
    (min_le_right δ (min 1 (R / 2))).trans (min_le_left 1 (R / 2))
  have hdist_upper : dist z 0 < R + 1 := by
    have := (abs_lt.mp hnear).2
    linarith
  have hzDisk : z ∈ pascalCenteredXiZeroDiskFinset (R + 1) := by
    rw [mem_pascalCenteredXiZeroDiskFinset_iff]
    exact ⟨Metric.mem_closedBall.mpr (le_of_lt hdist_upper), hz⟩
  have hzS : dist z 0 ∈ S := by
    exact Finset.mem_image.mpr ⟨z, hzDisk, rfl⟩
  have hδbound := hδS (dist z 0) hzS
  have hε_le_δ : ε ≤ δ := min_le_left δ (min 1 (R / 2))
  have hstrict : |dist z 0 - R| < δ := lt_of_lt_of_le hnear hε_le_δ
  exact (not_lt_of_ge hδbound) hstrict

/-- A boundary-safe radius has a positive radial annulus containing no centered
Xi zero.  This is the finite-gap endpoint used to stabilize the window. -/
theorem exists_pascalCenteredXi_zeroFreeRadialAnnulus
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, |dist z 0 - R| < ε →
        pascalCenteredRiemannXiKernel z ≠ 0 := by
  obtain ⟨ε, hε, hgap⟩ := exists_safeRadius_radial_gap hR
  refine ⟨ε, hε, ?_⟩
  intro z hz hzero
  apply hgap z (mem_pascalCenteredXiZeros.mpr hzero)
  exact hz

private theorem exists_safeRadius_disk_stability
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, |r - R| < ε →
        pascalCenteredXiZeroDisk r = pascalCenteredXiZeroDisk R := by
  classical
  let S : Finset ℝ :=
    (pascalCenteredXiZeroDiskFinset (R + 1)).image (fun z : ℂ => dist z 0)
  have hRnot : R ∉ S := by
    intro hRmem
    rcases Finset.mem_image.mp hRmem with ⟨z, hz, hzr⟩
    have hzDisk := (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz)
    exact (hR.2 z (Metric.mem_sphere.mpr hzr))
      (mem_pascalCenteredXiZeros.mp hzDisk.2)
  obtain ⟨δ, hδ, hδS⟩ := exists_pos_finset_abs_sub_lower_bound S hRnot
  let ε : ℝ := min δ (min 1 (R / 2))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ (lt_min zero_lt_one (half_pos hR.1))
  refine ⟨ε, hε, ?_⟩
  intro r hr
  ext z
  rw [mem_pascalCenteredXiZeroDisk_iff, mem_pascalCenteredXiZeroDisk_iff]
  constructor
  · rintro ⟨hzr, hzzero⟩
    refine ⟨?_, hzzero⟩
    by_contra hnot
    have hRlt : R < dist z 0 := lt_of_not_ge hnot
    have hupper : dist z 0 < R + 1 := by
      have hrupper := (abs_lt.mp hr).2
      have hzle := Metric.mem_closedBall.mp hzr
      have hεle : ε ≤ 1 :=
        (min_le_right δ (min 1 (R / 2))).trans (min_le_left 1 (R / 2))
      linarith
    have hzS : dist z 0 ∈ S := by
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, rfl⟩
      rw [mem_pascalCenteredXiZeroDiskFinset_iff]
      exact ⟨Metric.mem_closedBall.mpr (le_of_lt hupper), hzzero⟩
    have hδbound := hδS (dist z 0) hzS
    have hnear : |dist z 0 - R| < ε := by
      rw [abs_of_pos (sub_pos.mpr hRlt)]
      have hzle := Metric.mem_closedBall.mp hzr
      linarith [(abs_lt.mp hr).2]
    exact (not_lt_of_ge (le_trans (min_le_left δ _) hδbound)) hnear
  · rintro ⟨hzR, hzzero⟩
    refine ⟨?_, hzzero⟩
    by_contra hnot
    have hrltd : r < dist z 0 := lt_of_not_ge hnot
    have hzS : dist z 0 ∈ S := by
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, rfl⟩
      rw [mem_pascalCenteredXiZeroDiskFinset_iff]
      exact ⟨Metric.mem_closedBall.mpr
          ((Metric.mem_closedBall.mp hzR).trans (by linarith)), hzzero⟩
    have hδbound := hδS (dist z 0) hzS
    have hnear : |dist z 0 - R| < ε := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Metric.mem_closedBall.mp hzR))]
      have hrlower := (abs_lt.mp hr).1
      linarith [Metric.mem_closedBall.mp hzR]
    exact (not_lt_of_ge (le_trans (min_le_left δ _) hδbound)) hnear

/-- The existing centered finite zero disk is locally constant at every
boundary-safe radius. -/
theorem exists_pascalCenteredXi_safeRadius_zeroDisk_stability
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, |r - R| < ε →
        pascalCenteredXiZeroDisk r = pascalCenteredXiZeroDisk R :=
  exists_safeRadius_disk_stability hR

/-- The repository's uncentered finite zero window is locally constant at a
boundary-safe radius.  This is the exact H1 window-stability statement. -/
theorem exists_pascalCenteredXi_safeRadius_window_stability
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, |r - R| < ε →
        pascalCriticalMirrorZeroWindow r = pascalCriticalMirrorZeroWindow R := by
  obtain ⟨ε, hε, hdisk⟩ := exists_pascalCenteredXi_safeRadius_zeroDisk_stability hR
  refine ⟨ε, hε, ?_⟩
  intro r hr
  have hdisk' := hdisk r hr
  ext s
  constructor
  · intro hs
    have hz : s - criticalLineCenter ∈ pascalCenteredXiZeroDisk r := by
      rw [mem_pascalCenteredXiZeroDisk_iff]
      refine ⟨?_, ?_⟩
      · simpa [dist_eq_norm] using (mem_pascalCriticalMirrorZeroWindow_iff.mp hs).1
      · exact (sub_center_mem_pascalCenteredXiZeros_iff_nontrivial s).mpr
          (mem_pascalCriticalMirrorZeroWindow_iff.mp hs).2
    rw [hdisk'] at hz
    rw [mem_pascalCriticalMirrorZeroWindow_iff]
    refine ⟨?_, ?_⟩
    · simpa [dist_eq_norm] using hz.1
    · exact (sub_center_mem_pascalCenteredXiZeros_iff_nontrivial s).mp hz.2
  · intro hs
    have hz : s - criticalLineCenter ∈ pascalCenteredXiZeroDisk R := by
      rw [mem_pascalCenteredXiZeroDisk_iff]
      refine ⟨?_, ?_⟩
      · simpa [dist_eq_norm] using (mem_pascalCriticalMirrorZeroWindow_iff.mp hs).1
      · exact (sub_center_mem_pascalCenteredXiZeros_iff_nontrivial s).mpr
          (mem_pascalCriticalMirrorZeroWindow_iff.mp hs).2
    rw [← hdisk'] at hz
    rw [mem_pascalCriticalMirrorZeroWindow_iff]
    refine ⟨?_, ?_⟩
    · simpa [dist_eq_norm] using hz.1
    · exact (sub_center_mem_pascalCenteredXiZeros_iff_nontrivial s).mp hz.2

end DkMath.RH.CFBRCProjection
