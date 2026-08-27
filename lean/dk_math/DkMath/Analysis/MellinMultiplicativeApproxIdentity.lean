/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCenteredDilation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# A multiplicative compact-support approximate identity for Mellin weights

For `ε > 0`, this module uses the ordinary function

```text
x ↦ (2 * ε)⁻¹ * x⁻¹ᐟ²
```

on the multiplicative box `[exp (-ε), exp ε]`, and zero outside that box.
The half-power is written with complex `cpow` on the positive real axis so
that it matches Mathlib's Mellin kernel.  The centered Mellin weight becomes a
logarithmic average of `exp (t * z)` and therefore tends pointwise to one as
the box shrinks.

This is an ordinary-function construction.  It does not use a Dirac measure,
distribution, hard spectral cutoff, or a global exact identity
`centeredMellinSpectralWeight h = 1`.  The finite-Xi and contour consequences
are kept in the CFBRC bridge module.
-/

namespace DkMath.Analysis

open Filter
open MeasureTheory
open Set
open scoped Interval Topology

/-! ## The centered multiplicative box -/

/-- The centered multiplicative box test function.

For positive `ε`, its support is the multiplicative interval
`[exp (-ε), exp ε]`, and on that interval it is the half-power normalized by
`(2 * ε)⁻¹`.  Nonpositive `ε` is totalized by the zero function; all analytic
theorems below explicitly assume `0 < ε`. -/
noncomputable def centeredMellinBoxApprox (ε : ℝ) (x : ℝ) : ℂ :=
  if 0 < ε ∧ x ∈ Set.Icc (Real.exp (-ε)) (Real.exp ε) then
    ((2 * ε : ℝ)⁻¹ : ℂ) * (x : ℂ) ^ (-(1 : ℂ) / 2)
  else 0

/-- The positive endpoints of the centered multiplicative box are ordered. -/
theorem centeredMellinBoxApprox_endpoints_ordered
    {ε : ℝ} (_hε : 0 < ε) :
    Real.exp (-ε) ≤ Real.exp ε := by
  apply Real.exp_le_exp.mpr
  linarith

/-- The box function has support in its positive multiplicative interval. -/
theorem centeredMellinBoxApprox_support_subset
    {ε : ℝ} (hε : 0 < ε) :
    Function.support (centeredMellinBoxApprox ε) ⊆
      Set.Icc (Real.exp (-ε)) (Real.exp ε) := by
  intro x hx
  have hxne : centeredMellinBoxApprox ε x ≠ 0 := by
    simpa [Function.mem_support] using hx
  have hx' : 0 < ε ∧ x ∈ Set.Icc (Real.exp (-ε)) (Real.exp ε) := by
    by_contra hnot
    rcases not_and_or.mp hnot with hnotε | hnotI
    · exact (hnotε hε).elim
    · apply hxne
      rw [centeredMellinBoxApprox, if_neg]
      intro hcond
      exact hnotI hcond.2
  exact hx'.2

/-- The box function is continuous on its supporting closed interval. -/
theorem centeredMellinBoxApprox_continuousOn
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (centeredMellinBoxApprox ε)
      (Set.Icc (Real.exp (-ε)) (Real.exp ε)) := by
  intro x hx
  have hxpos : 0 < x := by
    exact lt_of_lt_of_le (Real.exp_pos (-ε)) hx.1
  have hpow : ContinuousAt
      (fun y : ℝ => (y : ℂ) ^ (-(1 : ℂ) / 2)) x := by
    exact Complex.continuousAt_ofReal_cpow_const x (-(1 : ℂ) / 2)
      (Or.inr (ne_of_gt hxpos))
  have hbase : ContinuousWithinAt
      (fun y : ℝ => ((2 * ε : ℝ)⁻¹ : ℂ) *
        (y : ℂ) ^ (-(1 : ℂ) / 2))
      (Set.Icc (Real.exp (-ε)) (Real.exp ε)) x :=
    (continuousAt_const.mul hpow).continuousWithinAt
  have heq :
      (fun y : ℝ => ((2 * ε : ℝ)⁻¹ : ℂ) *
        (y : ℂ) ^ (-(1 : ℂ) / 2)) =ᶠ[
          𝓝[Set.Icc (Real.exp (-ε)) (Real.exp ε)] x]
      centeredMellinBoxApprox ε := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [centeredMellinBoxApprox, hε, hy]
  change Tendsto (centeredMellinBoxApprox ε)
    (𝓝[Set.Icc (Real.exp (-ε)) (Real.exp ε)] x)
    (𝓝 (centeredMellinBoxApprox ε x))
  simpa [centeredMellinBoxApprox, hε, hx] using hbase.congr' heq

/-- The centered box satisfies the generic compact-positive-support Mellin
convergence contract at every complex parameter. -/
theorem mellinConvergent_centeredMellinBoxApprox
    {ε : ℝ} (hε : 0 < ε) :
    ∀ s : ℂ, MellinConvergent (centeredMellinBoxApprox ε) s := by
  intro s
  exact mellinConvergent_of_support_subset_Icc_pos
    (Real.exp_pos (-ε))
    (centeredMellinBoxApprox_endpoints_ordered hε)
    (centeredMellinBoxApprox_support_subset hε)
    (centeredMellinBoxApprox_continuousOn hε) s

/-! ## Exact logarithmic Mellin representation -/

/-- The centered Mellin weight of the box is exactly the normalized
logarithmic average of the complex exponential.

The proof uses the interval-integral substitution `x = exp t`; the Jacobian
`exp t` cancels the half-power in the box and leaves `exp (t * z)`. -/
theorem centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) := by
  let lo : ℝ := Real.exp (-ε)
  let hi : ℝ := Real.exp ε
  let s : ℂ := (1 : ℂ) / 2 + z
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) •
    centeredMellinBoxApprox ε x
  let G : ℝ → ℂ := fun x => ((2 * ε : ℝ)⁻¹ : ℂ) •
    (x : ℂ) ^ (z - 1)
  have hlo : 0 < lo := by simp [lo, Real.exp_pos]
  have hhi : 0 < hi := by simp [hi, Real.exp_pos]
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact centeredMellinBoxApprox_endpoints_ordered hε
  have hF : IntegrableOn F (Set.Ioi 0) := by
    change IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) •
        centeredMellinBoxApprox ε x) (Set.Ioi 0)
    exact mellinConvergent_centeredMellinBoxApprox hε s
  have hFlo : IntegrableOn F (Set.Ioi lo) :=
    hF.mono_set (Set.Ioi_subset_Ioi hlo.le)
  have hFhi : IntegrableOn F (Set.Ioi hi) :=
    hF.mono_set (Set.Ioi_subset_Ioi hhi.le)
  have htail : (∫ x in Set.Ioi hi, F x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxnot : x ∉ Set.Icc lo hi := by
      exact fun hxi => (not_lt_of_ge hxi.2) hx
    have hcond : ¬ (0 < ε ∧ x ∈ Set.Icc
        (Real.exp (-ε)) (Real.exp ε)) := by
      intro h
      apply hxnot
      simpa [lo, hi] using h.2
    dsimp [F]
    rw [centeredMellinBoxApprox, if_neg hcond]
    simp
  have hbelow : (∫ x in (0 : ℝ)..lo, F x) = 0 := by
    have hEq : Set.EqOn F (fun _ => 0) (Set.Ioo (0 : ℝ) lo) := by
      intro x hx
      have hxnot : x ∉ Set.Icc lo hi := by
        intro hxi
        exact (not_lt_of_ge hxi.1) hx.2
      have hcond : ¬ (0 < ε ∧ x ∈ Set.Icc
          (Real.exp (-ε)) (Real.exp ε)) := by
        intro h
        apply hxnot
        simpa [lo, hi] using h.2
      dsimp [F]
      rw [centeredMellinBoxApprox]
      rw [if_neg hcond]
      simp
    rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hlo) hEq]
    simp
  have hsplit0 := intervalIntegral.integral_interval_add_Ioi hF hFlo
    (a := (0 : ℝ)) (b := lo)
  have hsplit1 := intervalIntegral.integral_interval_add_Ioi hFlo hFhi
    (a := lo) (b := hi)
  have hIoi : (∫ x in Set.Ioi 0, F x) = ∫ x in lo..hi, F x := by
    calc
      (∫ x in Set.Ioi 0, F x) =
          (∫ x in (0 : ℝ)..lo, F x) + ∫ x in Set.Ioi lo, F x :=
        hsplit0.symm
      _ = 0 + ((∫ x in lo..hi, F x) + ∫ x in Set.Ioi hi, F x) := by
        rw [hbelow, hsplit1]
      _ = ∫ x in lo..hi, F x := by rw [htail, zero_add, add_zero]
  have hGcont : ContinuousOn G (Real.exp '' Set.uIcc (-ε) ε) := by
    rintro y ⟨t, ht, rfl⟩
    have hy : 0 < Real.exp t := Real.exp_pos t
    have hpow : ContinuousAt
        (fun u : ℝ => (u : ℂ) ^ (z - 1)) (Real.exp t) :=
      Complex.continuousAt_ofReal_cpow_const (Real.exp t) (z - 1)
        (Or.inr (ne_of_gt hy))
    change ContinuousWithinAt
      (fun u : ℝ => ((2 * ε : ℝ)⁻¹ : ℂ) •
        (u : ℂ) ^ (z - 1)) (Real.exp '' Set.uIcc (-ε) ε) (Real.exp t)
    have hbase : ContinuousAt
        (fun u : ℝ => ((2 * ε : ℝ)⁻¹ : ℂ) •
          (u : ℂ) ^ (z - 1)) (Real.exp t) :=
      (show ContinuousAt (fun _ : ℝ => ((2 * ε : ℝ)⁻¹ : ℂ)) (Real.exp t)
        from continuousAt_const).smul hpow
    exact hbase.continuousWithinAt
  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (f := Real.exp) (f' := Real.exp) (g := G)
    (fun t _ => Real.hasDerivAt_exp t)
    Real.continuous_exp.continuousOn hGcont
  have hFG : (∫ x in lo..hi, F x) = ∫ x in Real.exp (-ε)..Real.exp ε, G x := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    have hx' : lo < x ∧ x < hi := by
      simpa [Set.uIoo_of_le hlohi] using hx
    have hxpos : 0 < x := by
      exact lt_of_lt_of_le hlo hx'.1.le
    have hxbox : x ∈ Set.Icc lo hi := by
      exact ⟨hx'.1.le, hx'.2.le⟩
    have hcpow : (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (-(1 : ℂ) / 2) =
        (x : ℂ) ^ (z - 1) := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hxpos))]
      dsimp [s]
      congr 1
      ring
    dsimp [F, G]
    have hxbox' : x ∈ Set.Icc (Real.exp (-ε)) (Real.exp ε) := by
      simpa [lo, hi] using hxbox
    rw [centeredMellinBoxApprox, if_pos (by exact ⟨hε, hxbox'⟩)]
    calc
      (x : ℂ) ^ (s - 1) *
          (((2 * ε : ℝ)⁻¹ : ℂ) * (x : ℂ) ^ (-(1 : ℂ) / 2)) =
          ((2 * ε : ℝ)⁻¹ : ℂ) *
            ((x : ℂ) ^ (s - 1) * (x : ℂ) ^ (-(1 : ℂ) / 2)) := by ring
      _ = ((2 * ε : ℝ)⁻¹ : ℂ) * (x : ℂ) ^ (z - 1) := by rw [hcpow]
  have hleft :
      (∫ t in (-ε)..ε, (Real.exp t : ℂ) •
          (G ∘ Real.exp) t) =
        ((2 * ε : ℝ)⁻¹ : ℂ) •
          (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hpow : ((Real.exp t : ℝ) : ℂ) ^ (z - 1) =
        Complex.exp ((t : ℂ) * (z - 1)) := by
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne')]
      rw [← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
    dsimp [G, Function.comp_def]
    rw [hpow]
    rw [Complex.ofReal_exp]
    calc
      Complex.exp ((t : ℂ)) *
          (((2 * ε : ℝ)⁻¹ : ℂ) * Complex.exp ((t : ℂ) * (z - 1))) =
          ((2 * ε : ℝ)⁻¹ : ℂ) *
            (Complex.exp ((t : ℂ)) *
              Complex.exp ((t : ℂ) * (z - 1))) := by ring
      _ = ((2 * ε : ℝ)⁻¹ : ℂ) * Complex.exp ((t : ℂ) * z) := by
        rw [← Complex.exp_add]
        congr 2
        ring
  have hright :
      (∫ x in Real.exp (-ε)..Real.exp ε, G x) =
        ((2 * ε : ℝ)⁻¹ : ℂ) •
          (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) := by
    rw [← hleft]
    simpa [smul_eq_mul] using hsub.symm
  change (∫ x in Set.Ioi 0, F x) = _
  rw [hIoi, hFG, hright]
  simp [smul_eq_mul]

/-- Rescaling the logarithmic box to `[-1,1]` removes the singular-looking
normalization factor and is the form used for the one-sided limit. -/
theorem centeredMellinBox_logAverage_rescale
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) =
      (1 / 2 : ℂ) *
        (∫ u in (-1 : ℝ)..1,
          Complex.exp (((ε * u : ℝ) : ℂ) * z)) := by
  have hscale := intervalIntegral.integral_deriv_smul_comp'
    (a := (-1 : ℝ)) (b := 1)
    (f := fun u : ℝ => ε * u) (f' := fun _ : ℝ => ε)
    (g := fun t : ℝ => Complex.exp ((t : ℂ) * z))
    (fun u _ => by simpa using (hasDerivAt_id u).const_mul ε)
    (by fun_prop) (by fun_prop)
  have hscale' :
      (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) =
        ∫ u in (-1 : ℝ)..1,
          (ε : ℝ) • Complex.exp (((ε * u : ℝ) : ℂ) * z) := by
    simpa [smul_eq_mul, mul_comm] using hscale.symm
  rw [hscale']
  rw [intervalIntegral.integral_smul]
  rw [Complex.real_smul]
  have harg : (fun x : ℝ => Complex.exp (((ε * x : ℝ) : ℂ) * z)) =
      (fun x : ℝ => Complex.exp (z * ((ε * x : ℝ) : ℂ))) := by
    funext x
    congr 1
    ring
  rw [harg]
  field_simp [hε.ne']
  rw [Complex.ofReal_mul]
  norm_num
  ring

/-- The centered Mellin box spectral weight converges to one at every fixed
complex spectral parameter along the positive epsilon filter. -/
theorem tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) z)
      (𝓝[>] 0) (𝓝 1) := by
  have hparam : Continuous fun ε : ℝ =>
      ∫ u in (-1 : ℝ)..1,
        Complex.exp (((ε * u : ℝ) : ℂ) * z) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) (-1 : ℝ) 1
  have hparam_lim : Tendsto
      (fun ε : ℝ =>
        ∫ u in (-1 : ℝ)..1,
          Complex.exp (((ε * u : ℝ) : ℂ) * z))
      (𝓝[>] 0) (𝓝 (2 : ℂ)) := by
    have hzero :
        (∫ u in (-1 : ℝ)..1,
          Complex.exp (((0 * u : ℝ) : ℂ) * z)) = (2 : ℂ) := by
      norm_num
    have ht := (hparam.continuousAt.tendsto (x := (0 : ℝ))).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa only [hzero] using ht
  have hmul :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 / 2 : ℂ)) (𝓝[>] 0) (𝓝 (1 / 2 : ℂ))).mul
      hparam_lim
  have htarget : Tendsto
      (fun ε : ℝ => (1 / 2 : ℂ) *
        ∫ u in (-1 : ℝ)..1,
          Complex.exp (((ε * u : ℝ) : ℂ) * z))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using hmul
  apply htarget.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε z,
    centeredMellinBox_logAverage_rescale hε z]

/-- Multiplying the approximate-identity spectral weight by `z²` realizes the
quadratic multiplier pointwise on the positive epsilon filter. -/
theorem tendsto_centeredMellinBoxApprox_quadraticWeight
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        z ^ 2 * centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) z)
      (𝓝[>] 0) (𝓝 (z ^ 2)) := by
  have hweight := tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one z
  have hconst : Tendsto (fun _ : ℝ => z ^ 2) (𝓝[>] 0) (𝓝 (z ^ 2)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hweight
  simpa using hmul

end DkMath.Analysis
