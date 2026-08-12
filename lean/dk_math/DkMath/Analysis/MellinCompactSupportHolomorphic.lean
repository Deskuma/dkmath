/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCompactSupport
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Holomorphic Mellin weights from positive compact support

This module upgrades the XDP-004 compact-positive-support convergence provider
to a globally differentiable Mellin transform.  The proof uses Mathlib's
`mellin_differentiableAt_of_isBigO_rpow`: compact support makes the function
identically zero near both Mellin endpoints, while continuity on the positive
compact interval supplies local integrability.

The centered spectral weight is the generic function
`z ↦ mellin h ((1 : ℂ) / 2 + z)`.  This file remains independent of Xi, zeta,
contours, explicit formulas, and RH.  In particular, holomorphicity of this
weight is not a realization of a hard radial cutoff and does not identify the
weight with `z ^ 2`.
-/

namespace DkMath.Analysis

open MeasureTheory
open Filter
open Set
open scoped Topology

private theorem mellin_locallyIntegrableOn_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    LocallyIntegrableOn h (Set.Ioi 0) := by
  have hIcc : IntegrableOn h (Set.Icc a b) :=
    hcont.integrableOn_compact isCompact_Icc
  have hIndicator : Integrable ((Set.Icc a b).indicator h) :=
    hIcc.integrable_indicator measurableSet_Icc
  have hIndicatorOn : IntegrableOn ((Set.Icc a b).indicator h) (Set.Ioi 0) :=
    hIndicator.integrableOn
  have heq : Set.EqOn h ((Set.Icc a b).indicator h) (Set.Ioi 0) := by
    intro x hx
    by_cases hxIcc : x ∈ Set.Icc a b
    · simp [Set.indicator_of_mem hxIcc]
    · have hxzero : h x = 0 := by
        by_contra hxne
        exact hxIcc (hsupp (by simpa [Function.mem_support] using hxne))
      simp [Set.indicator, hxIcc, hxzero]
  exact ((integrableOn_congr_fun heq measurableSet_Ioi).mpr hIndicatorOn).locallyIntegrableOn

private theorem mellin_eventuallyEq_zero_atTop_of_support_subset_Icc
    {h : ℝ → ℂ} {a b : ℝ}
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    h =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop b] with x hx
  by_contra hxne
  have hxIcc : x ∈ Set.Icc a b :=
    hsupp (by simpa [Function.mem_support] using hxne)
  exact (not_le_of_gt hx) hxIcc.2

private theorem mellin_eventuallyEq_zero_nhdsWithin_zero_of_support_subset_Icc
    {h : ℝ → ℂ} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    h =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
  have hIio : Set.Iio a ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds ha
  have hIioWithin : Set.Iio a ∈ 𝓝[>] (0 : ℝ) := by
    exact mem_nhdsWithin_of_mem_nhds hIio
  filter_upwards [hIioWithin] with x hx
  by_contra hxne
  have hxIcc : x ∈ Set.Icc a b :=
    hsupp (by simpa [Function.mem_support] using hxne)
  exact (not_le_of_gt hx) hxIcc.1

private theorem mellin_isBigO_atTop_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b A : ℝ}
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    h =O[atTop] (fun x : ℝ => x ^ (-A)) := by
  have hzero := mellin_eventuallyEq_zero_atTop_of_support_subset_Icc hsupp
  exact (Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    hzero.symm EventuallyEq.rfl

private theorem mellin_isBigO_nhdsWithin_zero_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b B : ℝ} (ha : 0 < a)
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-B)) := by
  have hzero := mellin_eventuallyEq_zero_nhdsWithin_zero_of_support_subset_Icc
    ha hsupp
  exact (Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-B))
      (𝓝[>] (0 : ℝ))).congr'
    hzero.symm EventuallyEq.rfl

/-- The Mellin transform of positive compact-support data is globally
differentiable for arbitrary complex parameters.

The hypotheses are exactly the XDP-004 support contract: `0 < a ≤ b`, support
inside `Icc a b`, and `ContinuousOn` on that interval.  Mathlib's
`mellin_differentiableAt_of_isBigO_rpow` is applied with exponents chosen on
either side of the requested real part; the support is eventually zero at both
endpoints, so no decay estimate stronger than compact support is required.
-/
theorem differentiable_mellin_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (_hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (fun s : ℂ => mellin h s) := by
  intro s
  let A : ℝ := s.re + 1
  let B : ℝ := s.re - 1
  have hfc : LocallyIntegrableOn h (Set.Ioi 0) :=
    mellin_locallyIntegrableOn_of_support_subset_Icc_pos hsupp hcont
  have htop : h =O[atTop] (fun x : ℝ => x ^ (-A)) :=
    mellin_isBigO_atTop_of_support_subset_Icc_pos hsupp
  have hbot : h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-B)) :=
    mellin_isBigO_nhdsWithin_zero_of_support_subset_Icc_pos ha hsupp
  exact mellin_differentiableAt_of_isBigO_rpow hfc htop (by
    dsimp [A]
    linarith) hbot (by
    dsimp [B]
    linarith)

/-- The centered Mellin spectral weight associated with a real-to-complex test
function.  The generic center is written as `1 / 2`, avoiding any CFBRC
namespace dependency. -/
noncomputable def centeredMellinSpectralWeight (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  mellin h ((1 : ℂ) / 2 + z)

/-- Positive compact-support Mellin data produce a globally differentiable
centered spectral weight by affine composition. -/
theorem differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (centeredMellinSpectralWeight h) := by
  intro z
  change DifferentiableAt ℂ
    (fun z : ℂ => mellin h ((1 : ℂ) / 2 + z)) z
  exact (differentiableAt_comp_add_left ((1 : ℂ) / 2)).2
    (differentiable_mellin_of_support_subset_Icc_pos ha hab hsupp hcont
      ((1 : ℂ) / 2 + z))

/-- Pointwise form of centered Mellin-weight differentiability. -/
theorem differentiableAt_centeredMellinSpectralWeight_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) (z : ℂ) :
    DifferentiableAt ℂ (centeredMellinSpectralWeight h) z :=
  differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
    ha hab hsupp hcont z

/-- The centered Mellin spectral weight transforms under the multiplicative
critical mirror by centered complex conjugation.  This is an algebraic surface
for the XDP-003 reflection theorem; it is not a finite interpolation statement
and does not extend a finite zero-window identity to a global zero sum. -/
theorem centeredMellinSpectralWeight_mirror_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) (z : ℂ) :
    centeredMellinSpectralWeight (mellinCriticalMirror h) z =
      (starRingEnd ℂ) (centeredMellinSpectralWeight h
        (-(starRingEnd ℂ) z)) := by
  simpa only [centeredMellinSpectralWeight, sub_eq_add_neg] using
    mellin_mellinCriticalMirror_centered_of_support_subset_Icc_pos
      ha hab hsupp hcont z

end DkMath.Analysis
