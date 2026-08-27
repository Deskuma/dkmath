/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCriticalMirror
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Compact positive-support Mellin admissibility

This module supplies the generic H2-side convergence provider for the XDP
series.  A function is required to have support in a positive compact interval
`[a,b]`, with `0 < a ≤ b`, and to be continuous on that interval.  These
hypotheses make every Mellin kernel integrable on the positive ray.

`HasCompactSupport` alone is intentionally not used: compact support may touch
zero, where arbitrary complex Mellin exponents need not be integrable.

The module has no zeta, Xi, zero, RH, or explicit-formula content.  It also
does not identify a spectral radial cutoff with a Mellin transform.  Such a
realization remains a later interpolation problem.
-/

namespace DkMath.Analysis

open MeasureTheory
open Set

private theorem continuousOn_mellinKernel
    {a b : ℝ} (ha : 0 < a) (s : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Icc a b) := by
  intro t ht
  apply (Complex.continuousAt_ofReal_cpow_const t (s - 1) ?_).continuousWithinAt
  exact Or.inr (ne_of_gt (lt_of_lt_of_le ha ht.1))

private theorem integrableOn_mellinKernel_mul
    {h : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hsupp : {x : ℝ | 0 < x ∧ h x ≠ 0} ⊆ Icc a b)
    (hcont : ContinuousOn h (Icc a b)) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • h t) (Ioi 0) := by
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) • h t
  have hgcont : ContinuousOn g (Icc a b) := by
    exact (continuousOn_mellinKernel ha s).smul hcont
  have hgIcc : IntegrableOn g (Icc a b) :=
    hgcont.integrableOn_compact isCompact_Icc
  have hgind : Integrable ((Icc a b).indicator g) :=
    hgIcc.integrable_indicator measurableSet_Icc
  have hgindOn : IntegrableOn ((Icc a b).indicator g) (Ioi 0) :=
    hgind.integrableOn
  have heq : Set.EqOn g ((Icc a b).indicator g) (Ioi 0) := by
    intro t ht
    by_cases htIcc : t ∈ Icc a b
    · simp [Set.indicator_of_mem htIcc]
    · have hzero : h t = 0 := by
        by_contra hne
        exact htIcc (hsupp ⟨ht, hne⟩)
      simp [Set.indicator, htIcc, g, hzero]
  exact (integrableOn_congr_fun heq measurableSet_Ioi).mpr hgindOn

/-- Arbitrary complex Mellin parameters converge for positive compact support.

The support condition is explicit and includes a positive lower endpoint; the
continuity condition is only required on the supporting interval.
-/
theorem mellinConvergent_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    ∀ s : ℂ, MellinConvergent h s := by
  intro s
  apply integrableOn_mellinKernel_mul ha hab ?_ hcont s
  intro x hx
  exact hsupp (by simpa [Function.mem_support] using hx.2)

/-- Variant of the compact-support convergence theorem that records support
only on the positive Mellin integration domain. -/
theorem mellinConvergent_of_pos_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : {x : ℝ | 0 < x ∧ h x ≠ 0} ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    ∀ s : ℂ, MellinConvergent h s := by
  intro s
  exact integrableOn_mellinKernel_mul ha hab hsupp hcont s

/-- Positive support of the Mellin mirror is transported to the reciprocal
interval `[1 / b, 1 / a]`.  The statement is intentionally restricted to the
positive domain; the totalized definition of `mellinCriticalMirror` outside it
is not treated as a classical support identity.
-/
theorem mellinCriticalMirror_support_pos_subset
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    {x : ℝ | 0 < x ∧ mellinCriticalMirror h x ≠ 0} ⊆
      Set.Icc b⁻¹ a⁻¹ := by
  intro x hx
  have hxi : h x⁻¹ ≠ 0 := by
    intro hzero
    apply hx.2
    simp [mellinCriticalMirror, hzero]
  have hxi_support : x⁻¹ ∈ Function.support h := by
    simpa [Function.mem_support] using hxi
  have hxi_interval : x⁻¹ ∈ Set.Icc a b := hsupp hxi_support
  have hxpos : 0 < x := hx.1
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hxi_upper : 1 / x ≤ b := by simpa [one_div] using hxi_interval.2
  have hxi_lower : a ≤ 1 / x := by simpa [one_div] using hxi_interval.1
  have hleft : b⁻¹ ≤ x := by
    simpa [one_div] using (one_div_le hb hxpos).2 hxi_upper
  have hright : x ≤ a⁻¹ := by
    simpa [one_div] using (le_one_div hxpos ha).2 hxi_lower
  exact ⟨hleft, hright⟩

/-- The mirror is continuous on its reciprocal supporting interval when the
original function is continuous on its positive supporting interval. -/
theorem continuousOn_mellinCriticalMirror_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    ContinuousOn (mellinCriticalMirror h) (Set.Icc b⁻¹ a⁻¹) := by
  intro x hx
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hxpos : 0 < x := by
    exact lt_of_lt_of_le (inv_pos.mpr hb) hx.1
  have hxinv : x⁻¹ ∈ Set.Icc a b := by
    have hleft : a ≤ 1 / x := by
      exact (le_one_div hxpos ha).mp (by simpa [one_div] using hx.2)
    have hright : 1 / x ≤ b := by
      exact (one_div_le hb hxpos).mp (by simpa [one_div] using hx.1)
    have hleft' : a ≤ x⁻¹ := by simpa [one_div] using hleft
    have hright' : x⁻¹ ≤ b := by simpa [one_div] using hright
    exact ⟨hleft', hright'⟩
  have hinv : ContinuousWithinAt (fun y : ℝ => y⁻¹) (Set.Icc b⁻¹ a⁻¹) x := by
    exact (continuousAt_inv₀ (ne_of_gt hxpos)).continuousWithinAt
  have hh : ContinuousWithinAt h (Set.Icc a b) x⁻¹ := hcont x⁻¹ hxinv
  have hcomp : ContinuousWithinAt (fun y : ℝ => h y⁻¹)
      (Set.Icc b⁻¹ a⁻¹) x := by
    simpa only [Function.comp_def] using hh.comp hinv (by
        intro y hy
        exact (by
          have hypos : 0 < y := lt_of_lt_of_le (inv_pos.mpr hb) hy.1
          have hyinv : y⁻¹ ∈ Set.Icc a b := by
            have hyl : a ≤ 1 / y :=
              (le_one_div hypos ha).mp (by simpa [one_div] using hy.2)
            have hyr : 1 / y ≤ b :=
              (one_div_le hb hypos).mp (by simpa [one_div] using hy.1)
            have hyl' : a ≤ y⁻¹ := by simpa [one_div] using hyl
            have hyr' : y⁻¹ ≤ b := by simpa [one_div] using hyr
            exact ⟨hyl', hyr'⟩
          exact hyinv))
  unfold mellinCriticalMirror
  change ContinuousWithinAt
    (fun y : ℝ => (y⁻¹ : ℂ) * star (h y⁻¹)) (Set.Icc b⁻¹ a⁻¹) x
  have hcast : ContinuousWithinAt (fun y : ℝ => (y⁻¹ : ℂ))
      (Set.Icc b⁻¹ a⁻¹) x := by
    convert (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (continuousAt_inv₀ (ne_of_gt hxpos)).continuousWithinAt) using 1
    simp only [Function.comp_def, Complex.ofReal_inv]
  have hstar : ContinuousWithinAt (fun y : ℝ => star (h y⁻¹))
      (Set.Icc b⁻¹ a⁻¹) x := by
    simpa only [Function.comp_def, starRingEnd_apply] using
      (Complex.continuous_conj.continuousAt).comp_continuousWithinAt hcomp
  exact hcast.mul hstar

/-- Every Mellin parameter is admissible for the critical mirror of positive
compact-support data. -/
theorem mellinConvergent_mellinCriticalMirror_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    ∀ s : ℂ, MellinConvergent (mellinCriticalMirror h) s := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hba : b⁻¹ ≤ a⁻¹ := by
    simpa only [inv_inv] using (inv_le_inv₀ hb ha).2 hab
  intro s
  exact mellinConvergent_of_pos_support_subset_Icc_pos
    (inv_pos.mpr hb) hba
    (mellinCriticalMirror_support_pos_subset ha hab hsupp)
    (continuousOn_mellinCriticalMirror_of_support_subset_Icc_pos ha hab hcont) s

/-- XDP-003 Mellin reflection with both convergence hypotheses supplied by
positive compact-support data. -/
theorem mellin_mellinCriticalMirror_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) (s : ℂ) :
    mellin (mellinCriticalMirror h) s =
      (starRingEnd ℂ) (mellin h (1 - (starRingEnd ℂ) s)) := by
  exact mellin_mellinCriticalMirror h s
    (mellinConvergent_mellinCriticalMirror_of_support_subset_Icc_pos
      ha hab hsupp hcont s)
    (mellinConvergent_of_support_subset_Icc_pos ha hab hsupp hcont
      (1 - (starRingEnd ℂ) s))

/-- Centered form of the compact-positive-support Mellin reflection. -/
theorem mellin_mellinCriticalMirror_centered_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) (z : ℂ) :
    mellin (mellinCriticalMirror h) ((1 : ℂ) / 2 + z) =
      (starRingEnd ℂ)
        (mellin h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) := by
  exact mellin_mellinCriticalMirror_centered h z
    (mellinConvergent_mellinCriticalMirror_of_support_subset_Icc_pos
      ha hab hsupp hcont ((1 : ℂ) / 2 + z))
    (mellinConvergent_of_support_subset_Icc_pos ha hab hsupp hcont
      ((1 : ℂ) / 2 - (starRingEnd ℂ) z))

end DkMath.Analysis
