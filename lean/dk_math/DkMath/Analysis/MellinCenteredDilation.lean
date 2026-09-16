/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCompactSupportHolomorphic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Centered Mellin dilation and symmetric second differences

For a positive real scale `λ`, `mellinDilate λ h x = h (x / λ)`.  With the
Mellin convention used by Mathlib this produces the exact multiplier
`λ ^ s`.  After centering at `s = 1 / 2 + z` and removing the half-weight, a
logarithmic dilation `λ = exp τ` produces `exp (τ * z)`.

The symmetric second difference therefore converges pointwise to
`z ^ 2 * centeredMellinSpectralWeight h z`.  The factor
`centeredMellinSpectralWeight h z` is intentionally retained: this module does
not assert a global `z ^ 2` realization, use a Dirac delta, identify a hard
cutoff with a Mellin transform, or prove a defect or RH statement.
-/

namespace DkMath.Analysis

open Filter
open Set
open scoped Topology

/-! ## Positive multiplicative dilation -/

/-- The non-normalized positive multiplicative dilation of a Mellin test
function.  The definition is totalized on all real inputs, but its scaling
theorem is only stated for `0 < λ`. -/
noncomputable def mellinDilate (scale : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  h (x / scale)

/-- Support is transported from `[a,b]` to `[λa,λb]` by positive dilation. -/
theorem support_mellinDilate_subset
    {h : ℝ → ℂ} {a b scale : ℝ}
    (hscale : 0 < scale)
    (hsupp : Function.support h ⊆ Set.Icc a b) :
Function.support (mellinDilate scale h) ⊆
      Set.Icc (scale * a) (scale * b) := by
  intro x hx
  have hxdiv : x / scale ∈ Function.support h := by
    simpa [mellinDilate, Function.mem_support] using hx
  have hdiv := hsupp hxdiv
  constructor
  · simpa [mul_comm] using (le_div_iff₀ hscale).mp hdiv.1
  · simpa [mul_comm] using (div_le_iff₀ hscale).mp hdiv.2

/-- Continuity on the transported compact support interval. -/
theorem continuousOn_mellinDilate_of_support_subset
    {h : ℝ → ℂ} {a b scale : ℝ}
    (hscale : 0 < scale)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    ContinuousOn (mellinDilate scale h) (Set.Icc (scale * a) (scale * b)) := by
  intro x hx
  have hxdiv : x / scale ∈ Set.Icc a b := by
    constructor
    · apply (le_div_iff₀ hscale).mpr
      simpa [mul_comm] using hx.1
    · apply (div_le_iff₀ hscale).mpr
      simpa [mul_comm] using hx.2
  have hdiv : ContinuousWithinAt (fun y : ℝ => y / scale)
      (Set.Icc (scale * a) (scale * b)) x := by
    exact (continuousAt_id.div_const scale).continuousWithinAt
  change ContinuousWithinAt (fun y : ℝ => h (y / scale))
    (Set.Icc (scale * a) (scale * b)) x
  simpa only [Function.comp_def] using (hcont (x / scale) hxdiv).comp_of_eq hdiv (by
    intro y hy
    constructor
    · apply (le_div_iff₀ hscale).mpr
      simpa [mul_comm] using hy.1
    · apply (div_le_iff₀ hscale).mpr
      simpa [mul_comm] using hy.2) rfl

/-! ## Exact Mellin scaling -/

/-- Mellin scaling under positive multiplicative dilation.

The proof delegates the positive-ray change of variables to Mathlib's
`mellin_comp_mul_left`; the inverse scale is positive, and the resulting
complex `cpow` is normalized to `(λ : ℂ) ^ s`. -/
theorem mellin_mellinDilate
    {h : ℝ → ℂ} {scale : ℝ} (hscale : 0 < scale) (s : ℂ) :
    mellin (mellinDilate scale h) s =
      (scale : ℂ) ^ s * mellin h s := by
  unfold mellinDilate
  have hscale' := mellin_comp_mul_left h s (a := scale⁻¹) (inv_pos.mpr hscale)
  rw [show (fun t : ℝ => h (t / scale)) =
      (fun t : ℝ => h (scale⁻¹ * t)) by funext t; rw [div_eq_mul_inv, mul_comm]]
  rw [hscale']
  rw [smul_eq_mul]
  have hcast : ((scale⁻¹ : ℝ) : ℂ) = (scale : ℂ)⁻¹ := by norm_num
  have harg : (scale : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hscale.le]
    exact (ne_of_gt Real.pi_pos).symm
  rw [hcast, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

/-! ## Centered dilation and second difference -/

/-- The half-weight-normalized Mellin weight of the dilation by `exp τ`. -/
noncomputable def centeredMellinDilatedSpectralWeight
    (h : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(τ : ℂ) / 2) *
    centeredMellinSpectralWeight (mellinDilate (Real.exp τ) h) z

/-- Exact centered dilation scaling: the logarithmic dilation is the
exponential multiplier `exp (τ * z)`. -/
theorem centeredMellinDilatedSpectralWeight_eq
    {h : ℝ → ℂ} (τ : ℝ) (z : ℂ) :
    centeredMellinDilatedSpectralWeight h τ z =
      Complex.exp ((τ : ℂ) * z) * centeredMellinSpectralWeight h z := by
  unfold centeredMellinDilatedSpectralWeight centeredMellinSpectralWeight
  rw [mellin_mellinDilate (Real.exp_pos τ) ((1 : ℂ) / 2 + z)]
  have hpow (w : ℂ) : ((Real.exp τ : ℝ) : ℂ) ^ w =
      Complex.exp ((τ : ℂ) * w) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos τ).ne')]
    rw [← Complex.ofReal_log (Real.exp_pos τ).le, Real.log_exp]
  rw [hpow]
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- The symmetric second-difference Mellin weight, patched at `τ = 0` by its
quadratic target so that the family has a canonical value at the limit point. -/
noncomputable def centeredMellinSecondDifferenceWeight
    (h : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  if τ = 0 then
    z ^ 2 * centeredMellinSpectralWeight h z
  else
    (centeredMellinDilatedSpectralWeight h τ z -
        2 * centeredMellinSpectralWeight h z +
        centeredMellinDilatedSpectralWeight h (-τ) z) /
      (τ : ℂ) ^ 2

/-- Away from zero, the symmetric second difference is the exponential kernel
times the undilated centered Mellin weight. -/
theorem centeredMellinSecondDifferenceWeight_eq_kernel_mul
    {h : ℝ → ℂ} {τ : ℝ} {z : ℂ} (hτ : τ ≠ 0) :
    centeredMellinSecondDifferenceWeight h τ z =
      ((Complex.exp ((τ : ℂ) * z) - 2 +
          Complex.exp (-(τ : ℂ) * z)) /
        (τ : ℂ) ^ 2) * centeredMellinSpectralWeight h z := by
  rw [centeredMellinSecondDifferenceWeight, ite_eq_right hτ,
    centeredMellinDilatedSpectralWeight_eq,
    centeredMellinDilatedSpectralWeight_eq]
  rw [show ((-τ : ℝ) : ℂ) = -(τ : ℂ) by norm_num]
  have hneg : Complex.exp (-(τ : ℂ) * z) =
      Complex.exp (-(z * (τ : ℂ))) := by congr 1; ring
  rw [hneg]
  ring

/-- The pure complex exponential symmetric second-difference kernel. -/
noncomputable def complexExpSecondDifferenceKernel
    (τ : ℝ) (z : ℂ) : ℂ :=
  if τ = 0 then z ^ 2 else
    (Complex.exp ((τ : ℂ) * z) - 2 +
      Complex.exp (-(τ : ℂ) * z)) / (τ : ℂ) ^ 2

private noncomputable def complexExpSecondDifferenceRemainder (x : ℂ) : ℂ :=
  Complex.exp x - (1 + x + x ^ 2 / 2)

private theorem complexExpSecondDifferenceRemainder_isLittleO :
    (fun x : ℂ => complexExpSecondDifferenceRemainder x) =o[𝓝 0]
      (fun x : ℂ => x ^ 2) := by
  simpa [complexExpSecondDifferenceRemainder, Finset.sum_range_succ,
    Nat.factorial] using (Complex.exp_sub_sum_range_succ_isLittleO_pow 2)

/-- The pure exponential second-difference kernel tends to its quadratic
coefficient.  The proof uses Mathlib's cubic Taylor remainder estimate; the
patched value at zero agrees with the resulting limit rather than relying on
the totalized quotient there. -/
theorem tendsto_complexExpSecondDifferenceKernel_zero
    (z : ℂ) :
    Tendsto (fun τ : ℝ => complexExpSecondDifferenceKernel τ z)
      (𝓝 0) (𝓝 (z ^ 2)) := by
  have hquot : Tendsto
      (fun x : ℂ => complexExpSecondDifferenceRemainder x / x ^ 2)
      (𝓝 0) (𝓝 0) :=
    complexExpSecondDifferenceRemainder_isLittleO.tendsto_div_nhds_zero
  have hplus : Tendsto
      (fun τ : ℝ =>
        complexExpSecondDifferenceRemainder ((τ : ℂ) * z) /
          (τ : ℂ) ^ 2)
      (𝓝 0) (𝓝 0) := by
    by_cases hz : z = 0
    · simp [hz, complexExpSecondDifferenceRemainder]
    · have hτ : Tendsto (fun τ : ℝ => (τ : ℂ)) (𝓝 0) (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto
      have hx : Tendsto (fun τ : ℝ => (τ : ℂ) * z) (𝓝 0) (𝓝 0) := by
        simpa using hτ.mul tendsto_const_nhds
      have hcomp := hquot.comp hx
      have hmul := hcomp.mul_const (z ^ 2)
      have hmul' : Tendsto
          (fun τ : ℝ => complexExpSecondDifferenceRemainder ((τ : ℂ) * z) /
            ((τ : ℂ) * z) ^ 2 * z ^ 2)
          (𝓝 0) (𝓝 0) := by
        simpa [Function.comp_def] using hmul
      apply hmul'.congr'
      filter_upwards [] with τ
      by_cases hτ : τ = 0
      · simp [hτ, complexExpSecondDifferenceRemainder]
      · field_simp [hτ, hz]
  have hminus : Tendsto
      (fun τ : ℝ =>
        complexExpSecondDifferenceRemainder (-(τ : ℂ) * z) /
          (τ : ℂ) ^ 2)
      (𝓝 0) (𝓝 0) := by
    by_cases hz : z = 0
    · simp [hz, complexExpSecondDifferenceRemainder]
    · have hτ : Tendsto (fun τ : ℝ => (τ : ℂ)) (𝓝 0) (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto
      have hx : Tendsto (fun τ : ℝ => -(τ : ℂ) * z) (𝓝 0) (𝓝 0) := by
        simpa using hτ.neg.mul tendsto_const_nhds
      have hcomp := hquot.comp hx
      have hmul := hcomp.mul_const (z ^ 2)
      have hmul' : Tendsto
          (fun τ : ℝ => complexExpSecondDifferenceRemainder (-(τ : ℂ) * z) /
            (-(τ : ℂ) * z) ^ 2 * z ^ 2)
          (𝓝 0) (𝓝 0) := by
        simpa [Function.comp_def] using hmul
      apply hmul'.congr'
      filter_upwards [] with τ
      by_cases hτ : τ = 0
      · simp [hτ, complexExpSecondDifferenceRemainder]
      · field_simp [hτ, hz]
  have hsum : Tendsto
      (fun τ : ℝ => z ^ 2 +
        complexExpSecondDifferenceRemainder ((τ : ℂ) * z) /
          (τ : ℂ) ^ 2 +
        complexExpSecondDifferenceRemainder (-(τ : ℂ) * z) /
          (τ : ℂ) ^ 2)
      (𝓝 0) (𝓝 (z ^ 2)) := by
    simpa using (tendsto_const_nhds.add hplus).add hminus
  apply hsum.congr'
  filter_upwards [] with τ
  by_cases hτ : τ = 0
  · simp [complexExpSecondDifferenceKernel, hτ,
      complexExpSecondDifferenceRemainder]
  · rw [complexExpSecondDifferenceKernel, ite_eq_right hτ]
    unfold complexExpSecondDifferenceRemainder
    rw [show -(τ : ℂ) * z = -(z * (τ : ℂ)) by ring]
    field_simp [hτ]
    ring_nf

/-- The centered Mellin second difference converges pointwise to the
quadratic multiplier times the original centered Mellin weight. -/
theorem tendsto_centeredMellinSecondDifferenceWeight_zero
    {h : ℝ → ℂ} (z : ℂ) :
    Tendsto
      (fun τ : ℝ => centeredMellinSecondDifferenceWeight h τ z)
      (𝓝 0)
      (𝓝 (z ^ 2 * centeredMellinSpectralWeight h z)) := by
  have hkernel := tendsto_complexExpSecondDifferenceKernel_zero z
  have hmul := hkernel.mul_const (centeredMellinSpectralWeight h z)
  apply hmul.congr'
  filter_upwards [] with τ
  by_cases hτ : τ = 0
  · simp [centeredMellinSecondDifferenceWeight, complexExpSecondDifferenceKernel,
      hτ]
  · rw [centeredMellinSecondDifferenceWeight_eq_kernel_mul hτ]
    rw [complexExpSecondDifferenceKernel, ite_eq_right hτ]

/-- Every patched centered Mellin second-difference weight is entire under the
same positive compact-support contract as the undilated Mellin weight.  At
`τ = 0` this is the polynomially weighted target; away from zero it follows
from the exact exponential representation. -/
theorem differentiable_centeredMellinSecondDifferenceWeight
    {h : ℝ → ℂ} {a b τ : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (centeredMellinSecondDifferenceWeight h τ) := by
  have hH := differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
    ha hab hsupp hcont
  by_cases hτ : τ = 0
  · rw [show centeredMellinSecondDifferenceWeight h τ =
        (fun z => z ^ 2 * centeredMellinSpectralWeight h z) by
      funext z
      simp [centeredMellinSecondDifferenceWeight, hτ]]
    fun_prop
  · have hplus : Differentiable ℂ
        (centeredMellinDilatedSpectralWeight h τ) := by
      rw [show centeredMellinDilatedSpectralWeight h τ =
          (fun z => Complex.exp ((τ : ℂ) * z) *
            centeredMellinSpectralWeight h z) by
        funext z
        exact centeredMellinDilatedSpectralWeight_eq τ z]
      fun_prop
    have hminus : Differentiable ℂ
        (centeredMellinDilatedSpectralWeight h (-τ)) := by
      rw [show centeredMellinDilatedSpectralWeight h (-τ) =
          (fun z => Complex.exp (((-τ : ℝ) : ℂ) * z) *
            centeredMellinSpectralWeight h z) by
        funext z
        exact centeredMellinDilatedSpectralWeight_eq (-τ) z]
      fun_prop
    rw [show centeredMellinSecondDifferenceWeight h τ =
        (fun z =>
          (centeredMellinDilatedSpectralWeight h τ z -
              2 * centeredMellinSpectralWeight h z +
              centeredMellinDilatedSpectralWeight h (-τ) z) /
            (τ : ℂ) ^ 2) by
      funext z
      simp [centeredMellinSecondDifferenceWeight, hτ]]
    have hτc : (τ : ℂ) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hτ)
    fun_prop

end DkMath.Analysis
