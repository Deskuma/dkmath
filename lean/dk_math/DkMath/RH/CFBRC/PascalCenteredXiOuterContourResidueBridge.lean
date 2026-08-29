/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge"

/-!
# Finite-pole subtraction for the centered Xi outer contour

The outer formula in this module is proved by subtracting the finite principal
parts belonging to the Xi zeros in the closed disk.  A removable patch is
used at every zero before Cauchy-Goursat is applied.  In particular, the
totalized value of `logDeriv` at a zero is never identified with its removable
limit.

This module proves the fixed holomorphic outer formulas for arbitrary entire
weights, then specializes them to `1` and `z ^ 2`.  It does not identify the
holomorphic second moment with the non-holomorphic radial moment, and it does
not prove any RH or energy-vanishing statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Phase A: disk moments, outer observable, and principal parts -/

/-- The centered Xi disk moment against a holomorphic weight. -/
noncomputable def pascalCenteredXiZeroDiskWeightedMoment
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
    (pascalCenteredXiZeroMultiplicity a : ℂ) * h a

/-- The constant weight recovers the disk multiplicity mass. -/
@[simp] theorem pascalCenteredXiZeroDiskWeightedMoment_one (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment (fun _ => 1) R =
      (pascalCenteredXiZeroDiskMultiplicity R : ℂ) := by
  simp [pascalCenteredXiZeroDiskWeightedMoment,
    pascalCenteredXiZeroDiskMultiplicity]

/-- The weight `z ^ 2` recovers the centered complex second moment. -/
@[simp] theorem pascalCenteredXiZeroDiskWeightedMoment_second (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment pascalCenteredXiSecondWeight R =
      pascalCenteredXiZeroDiskSecondMoment R := by
  rfl

/-- The one-circle outer observable for a fixed holomorphic weight. -/
noncomputable def pascalCenteredXiWeightedOuterContourMass
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  circleIntegral (fun z => h z * pascalCenteredXiNegLogDeriv z) 0 R

/-- The principal part contributed by a centered Xi zero `a`. -/
noncomputable def pascalCenteredXiWeightedPrincipalPart
    (h : ℂ → ℂ) (a w : ℂ) : ℂ :=
  (-(pascalCenteredXiZeroMultiplicity a : ℂ) * h a) * (w - a)⁻¹

/-- The finite sum of all disk principal parts. -/
noncomputable def pascalCenteredXiDiskWeightedPrincipalPartSum
    (h : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
    pascalCenteredXiWeightedPrincipalPart h a w

/-- The unpatched difference of the outer integrand and its principal parts. -/
noncomputable def pascalCenteredXiDiskWeightedRawRegularizer
    (h : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  h w * pascalCenteredXiNegLogDeriv w -
    pascalCenteredXiDiskWeightedPrincipalPartSum h R w

/-! ## Phase B: one-pole expansion and cancellation -/

/-- Local logarithmic-derivative expansion at a centered Xi zero. -/
theorem exists_pascalCenteredXiNegLogDeriv_local_expansion
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeros) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g a ∧
      g a ≠ 0 ∧
      pascalCenteredXiNegLogDeriv =ᶠ[𝓝[≠] a]
        (fun w =>
          -(pascalCenteredXiZeroMultiplicity a : ℂ) * (w - a)⁻¹ -
            logDeriv g w) := by
  obtain ⟨g, hg, hg0, hfactor⟩ := exists_pascalCenteredXi_local_factorization ha
  let m : ℕ := pascalCenteredXiZeroMultiplicity a
  have hmpos : 0 < m := by
    simpa [m] using pascalCenteredXiZeroMultiplicity_pos ha
  have hfactor' : pascalCenteredRiemannXiKernel =ᶠ[𝓝[≠] a]
      (fun w => (w - a) ^ m * g w) := by
    simpa [m] using hfactor.filter_mono nhdsWithin_le_nhds
  have hg_ne : ∀ᶠ w in 𝓝[≠] a, g w ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hg_analytic : ∀ᶠ w in 𝓝[≠] a, AnalyticAt ℂ g w :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog : logDeriv pascalCenteredRiemannXiKernel =ᶠ[𝓝[≠] a]
      logDeriv (fun w => (w - a) ^ m * g w) :=
    hfactor'.nhdsNE_deriv.div hfactor'
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hlog, hg_ne, hg_analytic, self_mem_nhdsWithin] with w hw hgw hgwA hwmem
  have hwne : w - a ≠ 0 := sub_ne_zero.mpr (by simpa using hwmem)
  rw [pascalCenteredXiNegLogDeriv, hw]
  change -logDeriv ((fun u : ℂ => (u - a) ^ m) * g) w =
    -↑(pascalCenteredXiZeroMultiplicity a) * (w - a)⁻¹ - logDeriv g w
  rw [logDeriv_mul (f := fun u : ℂ => (u - a) ^ m) (g := g) w
    (pow_ne_zero m hwne) hgw (by fun_prop) hgwA.differentiableAt]
  have hderiv : deriv (fun u : ℂ => (u - a) ^ m) w =
      (m : ℂ) * (w - a) ^ (m - 1) := by
    convert (((hasDerivAt_id w).sub_const a).pow m).deriv using 1 <;> simp
  have hpow : (w - a) ^ m = (w - a) ^ (m - 1) * (w - a) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmpos)]
  simp only [logDeriv_apply, hderiv]
  rw [hpow]
  field_simp
  ring

/-- The weighted principal part cancels the selected Xi pole on a punctured neighborhood. -/
theorem exists_tendsto_pascalCenteredXiWeightedOwnPoleCanceled
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeros) :
    ∃ L : ℂ,
      Tendsto
        (fun w => h w * pascalCenteredXiNegLogDeriv w -
          pascalCenteredXiWeightedPrincipalPart h a w)
        (𝓝[≠] a) (𝓝 L) := by
  obtain ⟨g, hg, hg0, hexp⟩ := exists_pascalCenteredXiNegLogDeriv_local_expansion ha
  let m : ℕ := pascalCenteredXiZeroMultiplicity a
  let L : ℂ := -(m : ℂ) * deriv h a - h a * logDeriv g a
  have hlogg : Tendsto (logDeriv g) (𝓝[≠] a) (𝓝 (logDeriv g a)) := by
    change Tendsto (deriv g / g) (𝓝[≠] a) (𝓝 (deriv g a / g a))
    exact (hg.deriv.continuousAt.tendsto.div hg.continuousAt.tendsto hg0).mono_left
      nhdsWithin_le_nhds
  have hslope : Tendsto (slope h a) (𝓝[≠] a) (𝓝 (deriv h a)) :=
    (hh a).hasDerivAt.tendsto_slope
  have hhlim : Tendsto h (𝓝[≠] a) (𝓝 (h a)) :=
    (hh a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨L, ?_⟩
  have heq : (fun w => h w * pascalCenteredXiNegLogDeriv w -
      pascalCenteredXiWeightedPrincipalPart h a w) =ᶠ[𝓝[≠] a]
      (fun w => -(m : ℂ) * slope h a w - h w * logDeriv g w) := by
    filter_upwards [hexp, self_mem_nhdsWithin] with w hw hwmem
    have hwne : w - a ≠ 0 := sub_ne_zero.mpr (by simpa using hwmem)
    rw [hw]
    simp only [pascalCenteredXiWeightedPrincipalPart]
    rw [slope_fun_def_field]
    field_simp
    ring
  have hlim : Tendsto (fun w => -(m : ℂ) * slope h a w - h w * logDeriv g w)
      (𝓝[≠] a) (𝓝 L) := by
    simpa [L] using (tendsto_const_nhds.mul hslope).neg.sub (hhlim.mul hlogg)
  exact hlim.congr' heq.symm

/-- The raw finite-pole subtraction has a removable limit at every disk zero. -/
theorem exists_tendsto_pascalCenteredXiDiskWeightedRawRegularizer
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {a : ℂ}
    (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    ∃ L : ℂ,
      Tendsto (pascalCenteredXiDiskWeightedRawRegularizer h R)
        (𝓝[≠] a) (𝓝 L) := by
  let S := pascalCenteredXiZeroDiskFinset R
  have haS : a ∈ S := ha
  obtain ⟨Lown, hown⟩ := exists_tendsto_pascalCenteredXiWeightedOwnPoleCanceled hh
    (mem_pascalCenteredXiZeros.mpr (mem_pascalCenteredXiZeroDiskFinset_iff.mp ha).2)
  have hother : Tendsto
      (fun w => ∑ b ∈ S.erase a,
        pascalCenteredXiWeightedPrincipalPart h b w)
      (𝓝[≠] a) (𝓝 (∑ b ∈ S.erase a,
        pascalCenteredXiWeightedPrincipalPart h b a)) := by
    apply tendsto_finsetSum
    intro b hb
    have hba : a ≠ b := (Finset.mem_erase.mp hb).1.symm
    have hcont : ContinuousAt (pascalCenteredXiWeightedPrincipalPart h b) a := by
      unfold pascalCenteredXiWeightedPrincipalPart
      exact continuousAt_const.mul
        ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hba))
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hdecomp : pascalCenteredXiDiskWeightedRawRegularizer h R =ᶠ[𝓝[≠] a]
      (fun w =>
        (h w * pascalCenteredXiNegLogDeriv w -
          pascalCenteredXiWeightedPrincipalPart h a w) -
          ∑ b ∈ S.erase a,
            pascalCenteredXiWeightedPrincipalPart h b w) := by
    filter_upwards [] with w
    unfold pascalCenteredXiDiskWeightedRawRegularizer
    unfold pascalCenteredXiDiskWeightedPrincipalPartSum
    rw [← Finset.sum_erase_add S
      (fun b => pascalCenteredXiWeightedPrincipalPart h b w) haS]
    ring
  refine ⟨Lown - ∑ b ∈ S.erase a,
      pascalCenteredXiWeightedPrincipalPart h b a, ?_⟩
  have hlim := hown.sub hother
  exact hlim.congr' hdecomp.symm

/-- A chosen removable value for the raw regularizer at a disk zero.

The definition deliberately leaves the totalized raw value at a nonzero-free
point untouched; no equality between a totalized pole value and this limit is
assumed. -/
noncomputable def pascalCenteredXiDiskWeightedRawRegularizerLimit
    (h : ℂ → ℂ) (R : ℝ) (a : ℂ) : ℂ :=
  by
    classical
    exact if hh : Differentiable ℂ h then
      if ha : a ∈ pascalCenteredXiZeroDiskFinset R then
        Classical.choose (exists_tendsto_pascalCenteredXiDiskWeightedRawRegularizer hh ha)
      else 0
    else 0

/-- The chosen raw-regularizer value realizes the punctured-neighborhood limit. -/
theorem pascalCenteredXiDiskWeightedRawRegularizerLimit_spec
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    Tendsto (pascalCenteredXiDiskWeightedRawRegularizer h R)
      (𝓝[≠] a) (𝓝 (pascalCenteredXiDiskWeightedRawRegularizerLimit h R a)) := by
  classical
  simp only [pascalCenteredXiDiskWeightedRawRegularizerLimit, dite_eq_left hh, dite_eq_left ha]
  exact Classical.choose_spec (exists_tendsto_pascalCenteredXiDiskWeightedRawRegularizer hh ha)

/-! ## Phase C: finite removable patch -/

/-- Raw regularizer with the selected removable value inserted at every disk zero. -/
noncomputable def pascalCenteredXiDiskWeightedRegularizer
    (h : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  if w ∈ pascalCenteredXiZeroDiskFinset R then
    pascalCenteredXiDiskWeightedRawRegularizerLimit h R w
  else pascalCenteredXiDiskWeightedRawRegularizer h R w

/-- Near a selected zero, the patched regularizer is the corresponding function update. -/
theorem pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_update_at
    {h : ℂ → ℂ}
    {R : ℝ} {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    pascalCenteredXiDiskWeightedRegularizer h R =ᶠ[𝓝 a]
      Function.update (pascalCenteredXiDiskWeightedRawRegularizer h R) a
        (pascalCenteredXiDiskWeightedRawRegularizerLimit h R a) := by
  classical
  let S := pascalCenteredXiZeroDiskFinset R
  have havoid : ∀ᶠ w in 𝓝 a, w ∉ (S.erase a : Set ℂ) := by
    have havoid' : ∀ᶠ w in 𝓝 a, ∀ b ∈ (S.erase a : Set ℂ), w ≠ b := by
      refine (eventually_all_finite (S.erase a).finite_toSet).2 ?_
      intro b hb
      change b ∈ S.erase a at hb
      exact (isOpen_compl_singleton (x := b)).mem_nhds
        ((by exact (Finset.mem_erase.mp hb).1.symm) : a ≠ b)
    filter_upwards [havoid'] with w hw
    intro hwS
    exact hw w hwS rfl
  filter_upwards [havoid] with w hw
  by_cases hwa : w = a
  · subst w
    simp [pascalCenteredXiDiskWeightedRegularizer, Function.update, ha,
      pascalCenteredXiDiskWeightedRawRegularizerLimit]
  · have hwS : w ∉ S := by
      intro hwS
      exact hw (Finset.mem_erase.mpr ⟨hwa, hwS⟩)
    have hwS' : w ∉ pascalCenteredXiZeroDiskFinset R := by simpa [S] using hwS
    simp [pascalCenteredXiDiskWeightedRegularizer, Function.update, hwS', hwa]

/-- The finite patch restores continuity at every disk zero. -/
theorem pascalCenteredXiDiskWeightedRegularizer_continuousAt_of_mem
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    ContinuousAt (pascalCenteredXiDiskWeightedRegularizer h R) a := by
  rw [continuousAt_congr (pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_update_at ha)]
  exact continuousAt_update_same.mpr
    (pascalCenteredXiDiskWeightedRawRegularizerLimit_spec hh ha)

/-- A principal part is differentiable away from its center. -/
theorem differentiableAt_pascalCenteredXiWeightedPrincipalPart_of_ne
    {h : ℂ → ℂ} {a w : ℂ} (hwa : w ≠ a) :
    DifferentiableAt ℂ (pascalCenteredXiWeightedPrincipalPart h a) w := by
  unfold pascalCenteredXiWeightedPrincipalPart
  exact (differentiableAt_const (c := -(pascalCenteredXiZeroMultiplicity a : ℂ) * h a)).mul
    ((differentiableAt_id.sub (differentiableAt_const (c := a))).inv
      (sub_ne_zero.mpr hwa))

theorem continuousAt_pascalCenteredXiWeightedPrincipalPart_of_ne
    {h : ℂ → ℂ} {a w : ℂ} (hwa : w ≠ a) :
    ContinuousAt (pascalCenteredXiWeightedPrincipalPart h a) w := by
  exact (differentiableAt_pascalCenteredXiWeightedPrincipalPart_of_ne hwa).continuousAt

/-- A closed-disk point outside the classified zero finset is not a Xi zero. -/
theorem pascalCenteredXiKernel_ne_zero_of_mem_closedBall_not_mem_disk
    {R : ℝ} {w : ℂ} (hw : w ∈ Metric.closedBall 0 R)
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    pascalCenteredRiemannXiKernel w ≠ 0 := by
  intro hzero
  apply hwS
  rw [mem_pascalCenteredXiZeroDiskFinset_iff]
  exact ⟨hw, mem_pascalCenteredXiZeros.mpr hzero⟩

/-- The raw finite-pole regularizer is differentiable at any point where the
Xi kernel is nonzero and which is not one of the selected disk zeros.

This version separates the analytic nonvanishing input from the geometric
closed-ball argument used by the outer-circle proof.  It is the reusable
helper needed when a different contour, such as the finite rectangle, has
its own boundary/nonvanishing contract. -/
theorem differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer_of_kernel_ne_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {w : ℂ}
    (hXi : pascalCenteredRiemannXiKernel w ≠ 0)
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    DifferentiableAt ℂ (pascalCenteredXiDiskWeightedRawRegularizer h R) w := by
  have hlog : DifferentiableAt ℂ pascalCenteredXiNegLogDeriv w := by
    change DifferentiableAt ℂ (fun u => -logDeriv pascalCenteredRiemannXiKernel u) w
    exact (((analyticAt_pascalCenteredRiemannXiKernel w).deriv.differentiableAt.div
      (analyticAt_pascalCenteredRiemannXiKernel w).differentiableAt hXi).neg)
  have hsum : DifferentiableAt ℂ
      (pascalCenteredXiDiskWeightedPrincipalPartSum h R) w := by
    unfold pascalCenteredXiDiskWeightedPrincipalPartSum
    apply DifferentiableAt.fun_sum
    intro a ha
    exact differentiableAt_pascalCenteredXiWeightedPrincipalPart_of_ne
      (by intro hwa; exact hwS (by simpa [hwa] using ha))
  unfold pascalCenteredXiDiskWeightedRawRegularizer
  exact (hh w).mul hlog |>.sub hsum

theorem differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {w : ℂ} (hw : w ∈ Metric.closedBall 0 R)
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    DifferentiableAt ℂ (pascalCenteredXiDiskWeightedRawRegularizer h R) w := by
  have hXi := pascalCenteredXiKernel_ne_zero_of_mem_closedBall_not_mem_disk hw hwS
  have hlog : DifferentiableAt ℂ pascalCenteredXiNegLogDeriv w := by
    change DifferentiableAt ℂ (fun u => -logDeriv pascalCenteredRiemannXiKernel u) w
    exact (((analyticAt_pascalCenteredRiemannXiKernel w).deriv.differentiableAt.div
      (analyticAt_pascalCenteredRiemannXiKernel w).differentiableAt hXi).neg)
  have hsum : DifferentiableAt ℂ
      (pascalCenteredXiDiskWeightedPrincipalPartSum h R) w := by
    unfold pascalCenteredXiDiskWeightedPrincipalPartSum
    apply DifferentiableAt.fun_sum
    intro a ha
    exact differentiableAt_pascalCenteredXiWeightedPrincipalPart_of_ne
      (by intro hwa; exact hwS (by simpa [hwa] using ha))
  unfold pascalCenteredXiDiskWeightedRawRegularizer
  exact (hh w).mul hlog |>.sub hsum

theorem continuousAt_pascalCenteredXiDiskWeightedRawRegularizer
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {w : ℂ} (hw : w ∈ Metric.closedBall 0 R)
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    ContinuousAt (pascalCenteredXiDiskWeightedRawRegularizer h R) w := by
  exact (differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer hh hw hwS).continuousAt

theorem pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_raw_of_not_mem
    {h : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    pascalCenteredXiDiskWeightedRegularizer h R =ᶠ[𝓝 w]
      pascalCenteredXiDiskWeightedRawRegularizer h R := by
  classical
  let S := pascalCenteredXiZeroDiskFinset R
  have havoid : ∀ᶠ x in 𝓝 w, x ∉ (S : Set ℂ) := by
    have havoid' : ∀ᶠ x in 𝓝 w, ∀ a ∈ (S : Set ℂ), x ≠ a := by
      refine (eventually_all_finite S.finite_toSet).2 ?_
      intro a ha
      exact (isOpen_compl_singleton (x := a)).mem_nhds
        ((by
          have ha' : a ∈ pascalCenteredXiZeroDiskFinset R := by simpa [S] using ha
          exact fun hwa => hwS (by simpa [hwa] using ha')) : w ≠ a)
    filter_upwards [havoid'] with x hx
    intro hxS
    have hxS' : x ∈ S := by simpa using hxS
    exact hx x hxS' rfl
  filter_upwards [havoid] with x hx
  have hxS : x ∉ pascalCenteredXiZeroDiskFinset R := by simpa [S] using hx
  simp only [pascalCenteredXiDiskWeightedRegularizer, ite_eq_right hxS]

/-- The patched regularizer is continuous on the whole closed disk. -/
theorem pascalCenteredXiDiskWeightedRegularizer_continuousOn_closedBall
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} :
    ContinuousOn (pascalCenteredXiDiskWeightedRegularizer h R)
      (Metric.closedBall 0 R) := by
  intro w hw
  by_cases hwS : w ∈ pascalCenteredXiZeroDiskFinset R
  · exact (pascalCenteredXiDiskWeightedRegularizer_continuousAt_of_mem hh hwS).continuousWithinAt
  · have heq : pascalCenteredXiDiskWeightedRegularizer h R =ᶠ[
        𝓝[Metric.closedBall 0 R] w] pascalCenteredXiDiskWeightedRawRegularizer h R :=
      (pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_raw_of_not_mem
        (h := h) hwS).filter_mono nhdsWithin_le_nhds
    exact (heq.congr_continuousWithinAt_of_mem hw).2
      (continuousAt_pascalCenteredXiDiskWeightedRawRegularizer hh hw hwS).continuousWithinAt

/-- Off the finite exceptional set, the patched regularizer is differentiable in the open disk. -/
theorem pascalCenteredXiDiskWeightedRegularizer_differentiableAt_of_mem_ball_not_mem
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball 0 R)
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    DifferentiableAt ℂ (pascalCenteredXiDiskWeightedRegularizer h R) w := by
  have hwclosed : w ∈ Metric.closedBall 0 R := Metric.mem_closedBall.mpr
    (le_of_lt (Metric.mem_ball.mp hw))
  apply (pascalCenteredXiDiskWeightedRegularizer_eventuallyEq_raw_of_not_mem hwS).differentiableAt_iff.mpr
  exact differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer hh hwclosed hwS

/-- Boundary safety makes the patched and raw regularizers equal on the outer sphere. -/
theorem pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_sphere
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    Set.EqOn (pascalCenteredXiDiskWeightedRegularizer h R)
      (pascalCenteredXiDiskWeightedRawRegularizer h R) (Metric.sphere 0 R) := by
  intro w hw
  have hwS : w ∉ pascalCenteredXiZeroDiskFinset R := by
    intro hwS
    exact hR.2 w hw (mem_pascalCenteredXiZeros.mp
      (mem_pascalCenteredXiZeroDiskFinset_iff.mp hwS).2)
  simp [pascalCenteredXiDiskWeightedRegularizer, hwS]

/-! ## Phase E: Cauchy-Goursat for the patched regularizer -/

/-- Cauchy-Goursat annihilates the patched regularizer outer integral. -/
theorem circleIntegral_pascalCenteredXiDiskWeightedRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    circleIntegral (pascalCenteredXiDiskWeightedRegularizer h R) 0 R = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.1.le
    (pascalCenteredXiZeroDiskFinset R).countable_toSet
  · exact pascalCenteredXiDiskWeightedRegularizer_continuousOn_closedBall hh
  · intro w hw
    exact pascalCenteredXiDiskWeightedRegularizer_differentiableAt_of_mem_ball_not_mem
      hh hw.1 hw.2

/-- The raw regularizer has the same zero outer integral by sphere congruence. -/
theorem circleIntegral_pascalCenteredXiDiskWeightedRawRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    circleIntegral (pascalCenteredXiDiskWeightedRawRegularizer h R) 0 R = 0 := by
  rw [← circleIntegral.integral_congr hR.1.le
    (pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_sphere hR)]
  exact circleIntegral_pascalCenteredXiDiskWeightedRegularizer_eq_zero hh hR

/-! ## Phase F: principal-part circle integrals -/

theorem mem_pascalCenteredXiZeroDiskFinset_ball_of_boundarySafe
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R)
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    a ∈ Metric.ball 0 R :=
  (mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe hR).mp ha |>.1

/-- The outer circle integral of one principal part is its signed residue charge. -/
theorem circleIntegral_pascalCenteredXiWeightedPrincipalPart_eq
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R)
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    circleIntegral (pascalCenteredXiWeightedPrincipalPart h a) 0 R =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity a : ℂ) * h a := by
  have haBall := mem_pascalCenteredXiZeroDiskFinset_ball_of_boundarySafe hR ha
  unfold pascalCenteredXiWeightedPrincipalPart
  change circleIntegral
      (fun w => (-(pascalCenteredXiZeroMultiplicity a : ℂ) * h a) * (w - a)⁻¹) 0 R = _
  rw [circleIntegral.integral_const_mul]
  rw [circleIntegral.integral_sub_inv_of_mem_ball haBall]
  ring

theorem circleIntegrable_pascalCenteredXiWeightedPrincipalPart
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R)
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    CircleIntegrable (pascalCenteredXiWeightedPrincipalPart h a) 0 R := by
  apply ContinuousOn.circleIntegrable hR.1.le
  have haBall := mem_pascalCenteredXiZeroDiskFinset_ball_of_boundarySafe hR ha
  intro z hz
  have hza : ∀ z ∈ Metric.sphere (0 : ℂ) R, z ≠ a := by
    intro z hz hza
    subst z
    have hzR := Metric.mem_sphere.mp hz
    have haR := Metric.mem_ball.mp haBall
    linarith
  unfold pascalCenteredXiWeightedPrincipalPart
  exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀
    (fun z hz => sub_ne_zero.mpr (hza z hz))) z hz

theorem circleIntegrable_pascalCenteredXiDiskWeightedPrincipalPartSum
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    CircleIntegrable
      (pascalCenteredXiDiskWeightedPrincipalPartSum h R) 0 R := by
  unfold pascalCenteredXiDiskWeightedPrincipalPartSum
  apply CircleIntegrable.fun_sum
  intro a ha
  exact circleIntegrable_pascalCenteredXiWeightedPrincipalPart hR ha

/-- Summing the principal-part integrals gives the weighted disk moment. -/
theorem circleIntegral_pascalCenteredXiDiskWeightedPrincipalPartSum_eq
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    circleIntegral (pascalCenteredXiDiskWeightedPrincipalPartSum h R) 0 R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h R := by
  unfold pascalCenteredXiDiskWeightedPrincipalPartSum
  rw [circleIntegral.integral_fun_sum]
  · have hsum :
        (∑ a ∈ pascalCenteredXiZeroDiskFinset R,
          circleIntegral (pascalCenteredXiWeightedPrincipalPart h a) 0 R) =
          ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
            (-(2 * Real.pi * Complex.I) *
              (pascalCenteredXiZeroMultiplicity a : ℂ) * h a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact circleIntegral_pascalCenteredXiWeightedPrincipalPart_eq hR ha
    rw [hsum]
    calc
      (∑ a ∈ pascalCenteredXiZeroDiskFinset R,
          -(2 * Real.pi * Complex.I) *
            (pascalCenteredXiZeroMultiplicity a : ℂ) * h a) =
          ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
            (-(2 * Real.pi * Complex.I)) *
              ((pascalCenteredXiZeroMultiplicity a : ℂ) * h a) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = -(2 * Real.pi * Complex.I) *
          ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
            (pascalCenteredXiZeroMultiplicity a : ℂ) * h a := by
        rw [Finset.mul_sum]
      _ = -(2 * Real.pi * Complex.I) *
          pascalCenteredXiZeroDiskWeightedMoment h R := by
        rfl
  · intro a ha
    exact circleIntegrable_pascalCenteredXiWeightedPrincipalPart hR ha

/-! ## Phase G: the generic one-outer-contour residue formula -/

theorem circleIntegrable_pascalCenteredXiWeightedOuterIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    CircleIntegrable (fun z => h z * pascalCenteredXiNegLogDeriv z) 0 R := by
  apply ContinuousOn.circleIntegrable hR.1.le
  intro z hz
  exact (hh z).continuousAt.continuousWithinAt.mul
    (pascalCenteredXiNegLogDeriv_continuousOn_sphere hR z hz)

/-- The fixed outer Xi contour equals the finite weighted disk residue sum. -/
theorem pascalCenteredXiWeightedOuterContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass h R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h R := by
  have houter := circleIntegrable_pascalCenteredXiWeightedOuterIntegrand hh hR
  have hprincipal := circleIntegrable_pascalCenteredXiDiskWeightedPrincipalPartSum (h := h) hR
  have hraw : CircleIntegrable (pascalCenteredXiDiskWeightedRawRegularizer h R) 0 R := by
    have hEq : Set.EqOn (pascalCenteredXiDiskWeightedRawRegularizer h R)
        (pascalCenteredXiDiskWeightedRegularizer h R)
        (Metric.sphere (0 : ℂ) |R|) := by
      intro z hz
      have hz' : z ∈ Metric.sphere (0 : ℂ) R := by
        simpa [abs_of_pos hR.1] using hz
      exact (pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_sphere
        (h := h) (R := R) hR hz').symm
    rw [circleIntegrable_congr hEq]
    exact ContinuousOn.circleIntegrable hR.1.le
      (pascalCenteredXiDiskWeightedRegularizer_continuousOn_closedBall hh |>.mono
        Metric.sphere_subset_closedBall)
  unfold pascalCenteredXiWeightedOuterContourMass
  have hsplit : (fun z => h z * pascalCenteredXiNegLogDeriv z) =
      (fun z => pascalCenteredXiDiskWeightedRawRegularizer h R z +
        pascalCenteredXiDiskWeightedPrincipalPartSum h R z) := by
    funext z
    unfold pascalCenteredXiDiskWeightedRawRegularizer
    ring
  rw [hsplit, circleIntegral.integral_add hraw hprincipal,
    circleIntegral_pascalCenteredXiDiskWeightedRawRegularizer_eq_zero hh hR,
    circleIntegral_pascalCenteredXiDiskWeightedPrincipalPartSum_eq hR, zero_add]

/-- Normalizing the generic outer contour removes the factor `2 * π * I`. -/
theorem pascalCenteredXiNormalizedWeightedOuterContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ * pascalCenteredXiWeightedOuterContourMass h R =
      -pascalCenteredXiZeroDiskWeightedMoment h R := by
  rw [pascalCenteredXiWeightedOuterContourMass_eq hh hR]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

/-! ## Phase H/I: unweighted and `z ^ 2` specializations -/

/-- The unweighted outer contour counts centered Xi zero multiplicity with sign `-`. -/
theorem pascalCenteredXiOuterContourMass_eq_zeroDiskMultiplicity
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiOuterContourMass R =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroDiskMultiplicity R : ℂ) := by
  simpa [pascalCenteredXiOuterContourMass,
    pascalCenteredXiWeightedOuterContourMass] using
    pascalCenteredXiWeightedOuterContourMass_eq (h := fun _ : ℂ => (1 : ℂ))
      (by fun_prop) hR

theorem pascalCenteredXiNormalizedOuterContourMass_eq_zeroDiskMultiplicity
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ * pascalCenteredXiOuterContourMass R =
      -(pascalCenteredXiZeroDiskMultiplicity R : ℂ) := by
  simpa [pascalCenteredXiOuterContourMass,
    pascalCenteredXiWeightedOuterContourMass] using
    pascalCenteredXiNormalizedWeightedOuterContourMass_eq (h := fun _ : ℂ => (1 : ℂ))
      (by fun_prop) hR

/-- The normalized unweighted contour transports to the PPW window multiplicity. -/
theorem pascalCenteredXiNormalizedOuterContourMass_eq_windowMultiplicity
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ * pascalCenteredXiOuterContourMass R =
      -(pascalCriticalMirrorZeroWindowMultiplicity R : ℂ) := by
  rw [pascalCenteredXiNormalizedOuterContourMass_eq_zeroDiskMultiplicity hR,
    pascalCenteredXiZeroDiskMultiplicity_eq_windowMultiplicity]

/-- The one outer circle equals the existing finite local-contour mass. -/
theorem pascalCenteredXiOuterContourMass_eq_windowLocalContourMass
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiOuterContourMass R =
      pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass R := by
  rw [pascalCenteredXiOuterContourMass_eq_zeroDiskMultiplicity hR,
    pascalCenteredXiZeroDiskMultiplicity_eq_windowMultiplicity,
    pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass_eq]

/-- The `z ^ 2` outer contour equals the centered Xi second moment. -/
theorem pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiSecondOuterContourMass R =
      -(2 * Real.pi * Complex.I) * pascalCenteredXiZeroDiskSecondMoment R := by
  simpa [pascalCenteredXiSecondOuterContourMass,
    pascalCenteredXiWeightedOuterContourMass,
    pascalCenteredXiSecondWeight] using
    pascalCenteredXiWeightedOuterContourMass_eq (h := pascalCenteredXiSecondWeight)
      differentiable_pascalCenteredXiSecondWeight hR

/-- The normalized `z ^ 2` contour is the negative centered second moment. -/
theorem pascalCenteredXiNormalizedSecondOuterContourMass_eq_zeroDiskSecondMoment
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ * pascalCenteredXiSecondOuterContourMass R =
      -pascalCenteredXiZeroDiskSecondMoment R := by
  simpa [pascalCenteredXiSecondOuterContourMass,
    pascalCenteredXiWeightedOuterContourMass,
    pascalCenteredXiSecondWeight] using
    pascalCenteredXiNormalizedWeightedOuterContourMass_eq (h := pascalCenteredXiSecondWeight)
      differentiable_pascalCenteredXiSecondWeight hR

/-- The normalized second contour transports to the PPW centered second moment. -/
theorem pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ * pascalCenteredXiSecondOuterContourMass R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  rw [pascalCenteredXiNormalizedSecondOuterContourMass_eq_zeroDiskSecondMoment hR,
    pascalCenteredXiZeroDiskSecondMoment_eq_windowCenteredSecondMoment]

/-- The outer second contour equals the PPW local second-contour mass. -/
theorem pascalCenteredXiSecondOuterContourMass_eq_windowSecondLocalContourMass
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiSecondOuterContourMass R =
      pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass R := by
  rw [pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment hR,
    pascalCenteredXiZeroDiskSecondMoment_eq_windowCenteredSecondMoment,
    pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass]
  rw [pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass_eq
    differentiable_pascalCenteredXiSecondWeight]
  simp [pascalCenteredXiSecondWeight,
    pascalCriticalMirrorZeroWindowCenteredSecondMoment]

/-! ## Phase J: defect rewritten through the fixed outer Xi contour -/

/-- The finite second-moment defect can be written using the fixed outer Xi circle.

This is only a change of representation.  In particular, it does not assert
that the defect vanishes or that the radial moment is holomorphic. -/
theorem pascalSecondMomentDefect_eq_radial_sub_centeredXiOuter_re
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R -
        ((2 * Real.pi * Complex.I)⁻¹ *
          pascalCenteredXiSecondOuterContourMass R).re := by
  unfold pascalCriticalMirrorZeroWindowSecondMomentDefect
  have hcontour := pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass_eq R
  unfold pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass
  rw [hcontour,
    pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment hR]

end DkMath.RH.CFBRCProjection
