/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
import DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
import DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge"

/-!
# Centered Xi multiplicity transport and fixed local charges

This module transports analytic order from a nontrivial zeta zero to the
centered fixed Xi kernel.  It then reads that order with the fixed negative
logarithmic derivative on independently chosen isolating circles.

The finite sums below are sums of local circles.  They are intentionally not
identified with a single outer contour; that contour deformation and its
zero-set audit belong to the next checkpoint.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- The zero set of the fixed centered Xi kernel. -/
def pascalCenteredXiZeros : Set ℂ :=
  pascalCenteredRiemannXiKernel ⁻¹' {0}

@[simp] theorem mem_pascalCenteredXiZeros {z : ℂ} :
    z ∈ pascalCenteredXiZeros ↔ pascalCenteredRiemannXiKernel z = 0 :=
  Iff.rfl

/-- The centered Xi kernel is analytic at every point. -/
theorem analyticAt_pascalCenteredRiemannXiKernel (z : ℂ) :
    AnalyticAt ℂ pascalCenteredRiemannXiKernel z := by
  exact differentiable_pascalCenteredRiemannXiKernel.analyticAt z

theorem analyticOn_pascalCenteredRiemannXiKernel :
    AnalyticOnNhd ℂ pascalCenteredRiemannXiKernel Set.univ := by
  exact differentiable_pascalCenteredRiemannXiKernel.differentiableOn.analyticOnNhd isOpen_univ

@[simp] theorem pascalCenteredRiemannXiKernel_neg_center :
    pascalCenteredRiemannXiKernel (-criticalLineCenter) = -1 := by
  change pascalRiemannXiKernel (criticalLineCenter + -criticalLineCenter) = -1
  rw [add_neg_cancel]
  simp [pascalRiemannXiKernel]

theorem isClosed_pascalCenteredXiZeros :
    IsClosed pascalCenteredXiZeros := by
  have hcodiscrete : pascalCenteredXiZerosᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
    refine analyticOn_pascalCenteredRiemannXiKernel.preimage_zero_mem_codiscreteWithin
      (x := -criticalLineCenter) ?_ (Set.mem_univ _) isConnected_univ
    rw [pascalCenteredRiemannXiKernel_neg_center]
    norm_num
  simpa using (mem_codiscrete'.mp hcodiscrete).1

theorem isDiscrete_pascalCenteredXiZeros :
    IsDiscrete pascalCenteredXiZeros := by
  have hcodiscrete : pascalCenteredXiZerosᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
    refine analyticOn_pascalCenteredRiemannXiKernel.preimage_zero_mem_codiscreteWithin
      (x := -criticalLineCenter) ?_ (Set.mem_univ _) isConnected_univ
    rw [pascalCenteredRiemannXiKernel_neg_center]
    norm_num
  simpa using (mem_codiscrete'.mp hcodiscrete).2

theorem finite_pascalCenteredXiZeros_in_compact
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ pascalCenteredXiZeros).Finite := by
  apply (hK.inter_right isClosed_pascalCenteredXiZeros).finite
  exact isDiscrete_pascalCenteredXiZeros.mono Set.inter_subset_right

/-- Intrinsic finite multiplicity of a centered Xi zero. -/
noncomputable def pascalCenteredXiZeroMultiplicity (z : ℂ) : ℕ :=
  analyticOrderNatAt pascalCenteredRiemannXiKernel z

theorem analyticOrderAt_pascalCenteredXi_ne_top_of_mem
    {z : ℂ} (_hz : z ∈ pascalCenteredXiZeros) :
    analyticOrderAt pascalCenteredRiemannXiKernel z ≠ ⊤ := by
  apply AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    analyticOn_pascalCenteredRiemannXiKernel isPreconnected_univ
    (x := -criticalLineCenter) (y := z)
  · exact Set.mem_univ _
  · exact Set.mem_univ _
  · exact (analyticAt_pascalCenteredRiemannXiKernel _).analyticOrderAt_eq_zero.mpr
      (by rw [pascalCenteredRiemannXiKernel_neg_center]; norm_num) |>.trans_ne ENat.zero_ne_top

@[simp] theorem analyticOrderAt_pascalCenteredXi_eq_multiplicity
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    analyticOrderAt pascalCenteredRiemannXiKernel z =
      (pascalCenteredXiZeroMultiplicity z : ℕ∞) := by
  symm
  exact Nat.cast_analyticOrderNatAt
    (analyticOrderAt_pascalCenteredXi_ne_top_of_mem hz)

theorem pascalCenteredXiZeroMultiplicity_pos
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    0 < pascalCenteredXiZeroMultiplicity z := by
  apply Nat.pos_of_ne_zero
  intro hm
  have horder : analyticOrderAt pascalCenteredRiemannXiKernel z = 0 := by
    rw [analyticOrderAt_pascalCenteredXi_eq_multiplicity hz, hm]
    rfl
  exact (analyticAt_pascalCenteredRiemannXiKernel z).analyticOrderAt_ne_zero.mpr
    (mem_pascalCenteredXiZeros.mp hz) horder

/-- The polynomial factor in the local Xi/completed-zeta identity. -/
noncomputable def pascalXiPolynomialFactor (s : ℂ) : ℂ := s * (1 - s)

theorem analyticAt_pascalXiPolynomialFactor (s : ℂ) :
    AnalyticAt ℂ pascalXiPolynomialFactor s := by
  unfold pascalXiPolynomialFactor
  fun_prop

theorem pascalXiPolynomialFactor_ne_zero_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    pascalXiPolynomialFactor ρ ≠ 0 := by
  exact mul_ne_zero
    (ne_zero_of_pos_re (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).1)
    (sub_ne_zero.mpr (Ne.symm <| ne_one_of_re_lt_one
      (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).2))

theorem analyticOrderAt_pascalXiPolynomialFactor_eq_zero_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalXiPolynomialFactor ρ = 0 := by
  exact (analyticAt_pascalXiPolynomialFactor ρ).analyticOrderAt_eq_zero.mpr
    (pascalXiPolynomialFactor_ne_zero_of_nontrivial hρ)

theorem analyticAt_completedRiemannZeta_of_ne_zero_one
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hd : DifferentiableOn ℂ completedRiemannZeta ({0, 1}ᶜ : Set ℂ) := by
    intro w hw
    have hw' : w ≠ 0 ∧ w ≠ 1 := by simpa [Set.mem_compl_iff] using hw
    exact (differentiableAt_completedZeta hw'.1 hw'.2).differentiableWithinAt
  have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := by
    convert (isOpen_compl_singleton (x := (0 : ℂ))).inter
      (isOpen_compl_singleton (x := (1 : ℂ))) using 1
    ext w
    simp
  have hs : s ∈ ({0, 1}ᶜ : Set ℂ) := by
    simpa [Set.mem_compl_iff] using And.intro hs0 hs1
  exact hd.analyticAt (hopen.mem_nhds hs)

theorem analyticAt_GammaR_inv (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) s := by
  exact Complex.differentiable_Gammaℝ_inv.analyticAt s

theorem analyticOrderAt_pascalRiemannXiKernel_eq_completedRiemannZeta_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalRiemannXiKernel ρ =
      analyticOrderAt completedRiemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := ne_zero_of_pos_re
    (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).1
  have hρ1 : ρ ≠ 1 := ne_one_of_re_lt_one
    (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).2
  have hEq : pascalRiemannXiKernel =ᶠ[𝓝 ρ]
      (fun w => pascalXiPolynomialFactor w * completedRiemannZeta w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ0,
      isOpen_compl_singleton.mem_nhds hρ1] with w hw0 hw1
    exact pascalRiemannXiKernel_eq_mul_completedRiemannZeta hw0 hw1
  rw [analyticOrderAt_congr hEq]
  change analyticOrderAt (pascalXiPolynomialFactor * completedRiemannZeta) ρ = _
  rw [analyticOrderAt_mul (analyticAt_pascalXiPolynomialFactor ρ)
      (analyticAt_completedRiemannZeta_of_ne_zero_one hρ0 hρ1),
    analyticOrderAt_pascalXiPolynomialFactor_eq_zero_of_nontrivial hρ, zero_add]

theorem analyticOrderAt_completedRiemannZeta_eq_riemannZeta_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt completedRiemannZeta ρ =
      analyticOrderAt riemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := ne_zero_of_pos_re
    (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).1
  have hgamma : Complex.Gammaℝ ρ ≠ 0 := gammaR_ne_zero_of_pos_re
    (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).1
  have hEq : riemannZeta =ᶠ[𝓝 ρ]
      (fun w => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ0] with w hw0
    rw [riemannZeta_def_of_ne_zero hw0]
    ring
  rw [analyticOrderAt_congr hEq]
  change analyticOrderAt completedRiemannZeta ρ =
    analyticOrderAt (completedRiemannZeta * (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)) ρ
  rw [analyticOrderAt_mul
      (analyticAt_completedRiemannZeta_of_ne_zero_one hρ0
        (ne_one_of_re_lt_one (nontrivialRiemannZetaZero_mem_openCriticalStrip hρ).2))
      (analyticAt_GammaR_inv ρ)]
  have hinv : (Complex.Gammaℝ ρ)⁻¹ ≠ 0 := inv_ne_zero hgamma
  rw [(analyticAt_GammaR_inv ρ).analyticOrderAt_eq_zero.mpr hinv, add_zero]

@[simp] theorem analyticOrderAt_pascalRiemannXiKernel_eq_riemannZeta_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalRiemannXiKernel ρ =
      analyticOrderAt riemannZeta ρ := by
  exact (analyticOrderAt_pascalRiemannXiKernel_eq_completedRiemannZeta_of_nontrivial hρ).trans
    (analyticOrderAt_completedRiemannZeta_eq_riemannZeta_of_nontrivial hρ)

theorem analyticOrderAt_pascalCenteredXi_sub_center_eq_riemannZeta
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalCenteredRiemannXiKernel (ρ - criticalLineCenter) =
      analyticOrderAt riemannZeta ρ := by
  let g : ℂ → ℂ := fun z => criticalLineCenter + z
  have hg : AnalyticAt ℂ g (ρ - criticalLineCenter) := by
    exact ((differentiable_const (c := criticalLineCenter)).add differentiable_id).analyticAt _
  have hderiv : deriv g (ρ - criticalLineCenter) ≠ 0 := by
    simp [g]
  have hcomp : analyticOrderAt (pascalRiemannXiKernel ∘ g)
      (ρ - criticalLineCenter) = analyticOrderAt pascalRiemannXiKernel
        (g (ρ - criticalLineCenter)) :=
    analyticOrderAt_comp_of_deriv_ne_zero (f := pascalRiemannXiKernel) hg hderiv
  have harg : g (ρ - criticalLineCenter) = ρ := by
    simp [g]
  change analyticOrderAt (pascalRiemannXiKernel ∘ g)
      (ρ - criticalLineCenter) = analyticOrderAt riemannZeta ρ
  rw [hcomp, harg]
  exact analyticOrderAt_pascalRiemannXiKernel_eq_riemannZeta_of_nontrivial hρ

@[simp] theorem pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    pascalCenteredXiZeroMultiplicity (ρ - criticalLineCenter) =
      riemannZetaZeroMultiplicity ρ := by
  simpa [pascalCenteredXiZeroMultiplicity, riemannZetaZeroMultiplicity,
    analyticOrderNatAt] using congrArg ENat.toNat
      (analyticOrderAt_pascalCenteredXi_sub_center_eq_riemannZeta hρ)

theorem exists_pascalCenteredXi_local_factorization
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z ∧
      g z ≠ 0 ∧
      pascalCenteredRiemannXiKernel =ᶠ[𝓝 z]
        (fun w => (w - z) ^ pascalCenteredXiZeroMultiplicity z * g w) := by
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    (analyticAt_pascalCenteredRiemannXiKernel z).analyticOrderAt_ne_top.mp
      (analyticOrderAt_pascalCenteredXi_ne_top_of_mem hz)
  refine ⟨g, hg, hg0, ?_⟩
  simpa [pascalCenteredXiZeroMultiplicity, smul_eq_mul] using hfactor

theorem tendsto_mul_pascalCenteredXiNegLogDeriv_zeroMultiplicity
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    Tendsto
      (fun w => (w - z) * pascalCenteredXiNegLogDeriv w)
      (𝓝[≠] z)
      (𝓝 (-(pascalCenteredXiZeroMultiplicity z : ℂ))) := by
  obtain ⟨g, hg, hg0, hfactor⟩ := exists_pascalCenteredXi_local_factorization hz
  let m : ℕ := pascalCenteredXiZeroMultiplicity z
  have hmpos : 0 < m := by
    simpa [m] using pascalCenteredXiZeroMultiplicity_pos hz
  have hfactor' : pascalCenteredRiemannXiKernel =ᶠ[𝓝[≠] z]
      (fun w => (w - z) ^ m * g w) := by
    simpa [m] using hfactor.filter_mono nhdsWithin_le_nhds
  have hg_ne : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hg_analytic : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ g w :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog : logDeriv pascalCenteredRiemannXiKernel =ᶠ[𝓝[≠] z]
      logDeriv (fun w => (w - z) ^ m * g w) :=
    hfactor'.nhdsNE_deriv.div hfactor'
  have hlogg : Tendsto (logDeriv g) (𝓝[≠] z) (𝓝 (logDeriv g z)) := by
    change Tendsto (deriv g / g) (𝓝[≠] z) (𝓝 (deriv g z / g z))
    exact (hg.deriv.continuousAt.tendsto.div hg.continuousAt.tendsto hg0).mono_left
      nhdsWithin_le_nhds
  have hsub : Tendsto (fun w : ℂ => w - z) (𝓝[≠] z) (𝓝 0) := by
    convert
      ((tendsto_id.sub tendsto_const_nhds :
        Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 (z - z))).mono_left nhdsWithin_le_nhds) using 1 <;>
      simp
  have hregular : Tendsto (fun w => (w - z) * logDeriv g w)
      (𝓝[≠] z) (𝓝 0) := by
    simpa using hsub.mul hlogg
  have hmodel : Tendsto
      (fun w => (w - z) * (-logDeriv (fun u => (u - z) ^ m * g u) w))
      (𝓝[≠] z) (𝓝 (-(m : ℂ))) := by
    have hEq : (fun w => (w - z) * (-logDeriv (fun u => (u - z) ^ m * g u) w))
        =ᶠ[𝓝[≠] z] (fun w => -(m : ℂ) - (w - z) * logDeriv g w) := by
      filter_upwards [hg_ne, hg_analytic, self_mem_nhdsWithin] with w hw hgw hwmem
      have hwz : w - z ≠ 0 := sub_ne_zero.mpr (by simpa using hwmem)
      change (w - z) * -logDeriv ((fun u : ℂ => (u - z) ^ m) * g) w =
        -(m : ℂ) - (w - z) * logDeriv g w
      rw [logDeriv_mul (f := fun u : ℂ => (u - z) ^ m) (g := g) w
        (show (w - z) ^ m ≠ 0 from pow_ne_zero m hwz) hw
        (by fun_prop) hgw.differentiableAt]
      have hderiv : deriv (fun u : ℂ => (u - z) ^ m) w =
          (m : ℂ) * (w - z) ^ (m - 1) := by
        convert (((hasDerivAt_id w).sub_const z).pow m).deriv using 1 <;> simp
      have hpow : (w - z) ^ m = (w - z) ^ (m - 1) * (w - z) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmpos)]
      simp only [logDeriv_apply, hderiv]
      rw [hpow]
      field_simp
      ring
    refine (show Tendsto (fun w => -(m : ℂ) - (w - z) * logDeriv g w)
      (𝓝[≠] z) (𝓝 (-(m : ℂ))) by simpa using tendsto_const_nhds.sub hregular).congr' ?_
    exact hEq.symm
  refine hmodel.congr' ?_
  filter_upwards [hlog] with w hw
  simp only [pascalCenteredXiNegLogDeriv, hw]

theorem tendsto_mul_pascalCenteredXiNegLogDeriv_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    Tendsto
      (fun w =>
        (w - (ρ - criticalLineCenter)) * pascalCenteredXiNegLogDeriv w)
      (𝓝[≠] (ρ - criticalLineCenter))
      (𝓝 (-(riemannZetaZeroMultiplicity ρ : ℂ))) := by
  have hz : ρ - criticalLineCenter ∈ pascalCenteredXiZeros := by
    exact mem_pascalCenteredXiZeros.mpr
      (pascalCenteredRiemannXiKernel_sub_center_eq_zero_of_nontrivial hρ)
  convert tendsto_mul_pascalCenteredXiNegLogDeriv_zeroMultiplicity hz using 1
  rw [pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity hρ]

/-- A positive radius whose closed disk contains no centered Xi zero other than its center. -/
def IsPascalCenteredXiIsolatingRadius (z : ℂ) (r : ℝ) : Prop :=
  0 < r ∧
    ∀ w ∈ Metric.closedBall z r, w ≠ z → pascalCenteredRiemannXiKernel w ≠ 0

theorem exists_isPascalCenteredXiIsolatingRadius
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    ∃ r : ℝ, IsPascalCenteredXiIsolatingRadius z r := by
  obtain ⟨ε, hε, hεzeros⟩ :=
    Metric.exists_closedBall_inter_eq_singleton_of_discrete isDiscrete_pascalCenteredXiZeros hz
  refine ⟨ε, hε, ?_⟩
  intro w hw hwz hzero
  have hwinter : w ∈ Metric.closedBall z ε ∩ pascalCenteredXiZeros :=
    ⟨hw, mem_pascalCenteredXiZeros.mpr hzero⟩
  have : w = z := by
    simpa [hεzeros] using hwinter
  exact hwz this

/-- A chosen centered Xi isolating radius, with its specification exposed separately. -/
noncomputable def pascalCenteredXiIsolatingRadius (z : ℂ) : ℝ :=
  by
    classical
    exact if hz : z ∈ pascalCenteredXiZeros then
      Classical.choose (exists_isPascalCenteredXiIsolatingRadius hz)
    else 1

theorem pascalCenteredXiIsolatingRadius_spec
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    IsPascalCenteredXiIsolatingRadius z
      (pascalCenteredXiIsolatingRadius z) := by
  classical
  simp only [pascalCenteredXiIsolatingRadius, dite_eq_left hz]
  exact Classical.choose_spec (exists_isPascalCenteredXiIsolatingRadius hz)

theorem pascalCenteredXiIsolatingRadius_pos
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    0 < pascalCenteredXiIsolatingRadius z :=
  (pascalCenteredXiIsolatingRadius_spec hz).1

/-- The regular factor multiplying the Cauchy kernel at a centered Xi zero. -/
noncomputable def pascalCenteredXiLocalResidueKernel (z w : ℂ) : ℂ :=
  (w - z) * pascalCenteredXiNegLogDeriv w

theorem tendsto_pascalCenteredXiLocalResidueKernel
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    Tendsto (pascalCenteredXiLocalResidueKernel z) (𝓝[≠] z)
      (𝓝 (-(pascalCenteredXiZeroMultiplicity z : ℂ))) :=
  tendsto_mul_pascalCenteredXiNegLogDeriv_zeroMultiplicity hz

theorem pascalCenteredXiNegLogDeriv_eq_inv_mul_localResidueKernel
    {z w : ℂ} (hw : w ≠ z) :
    pascalCenteredXiNegLogDeriv w =
      (w - z)⁻¹ * pascalCenteredXiLocalResidueKernel z w := by
  rw [pascalCenteredXiLocalResidueKernel]
  field_simp

theorem differentiableAt_pascalCenteredXiLocalResidueKernel_of_isolatingRadius
    {z w : ℂ} {r : ℝ} (hr : IsPascalCenteredXiIsolatingRadius z r)
    (hw : w ∈ Metric.ball z r \ {z}) :
    DifferentiableAt ℂ (pascalCenteredXiLocalResidueKernel z) w := by
  have hwne : pascalCenteredRiemannXiKernel w ≠ 0 := hr.2 w
    (Metric.ball_subset_closedBall hw.1) (by simpa using hw.2)
  change DifferentiableAt ℂ (fun u => (u - z) * (-logDeriv pascalCenteredRiemannXiKernel u)) w
  exact (differentiableAt_id.sub_const z).mul
    ((analyticAt_pascalCenteredRiemannXiKernel w).deriv.differentiableAt.div
      (analyticAt_pascalCenteredRiemannXiKernel w).differentiableAt hwne).neg

theorem continuousOn_pascalCenteredXiLocalResidueKernel_of_isolatingRadius
    {z : ℂ} {r : ℝ} (hr : IsPascalCenteredXiIsolatingRadius z r) :
    ContinuousOn (pascalCenteredXiLocalResidueKernel z) (Metric.closedBall z r \ {z}) := by
  intro w hw
  have hwne : pascalCenteredRiemannXiKernel w ≠ 0 := hr.2 w hw.1 (by simpa using hw.2)
  change ContinuousWithinAt (fun u => (u - z) * (-logDeriv pascalCenteredRiemannXiKernel u))
    (Metric.closedBall z r \ {z}) w
  exact ((differentiableAt_id.sub_const z).mul
    ((analyticAt_pascalCenteredRiemannXiKernel w).deriv.differentiableAt.div
      (analyticAt_pascalCenteredRiemannXiKernel w).differentiableAt hwne).neg).continuousAt.continuousWithinAt

theorem circleIntegral_pascalCenteredXiNegLogDeriv_eq_of_isolatingRadius
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros)
    {r : ℝ} (hr : IsPascalCenteredXiIsolatingRadius z r) :
    circleIntegral pascalCenteredXiNegLogDeriv z r =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ) := by
  have hCauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      (c := z) (R := r) hr.1 Set.countable_empty
      (continuousOn_pascalCenteredXiLocalResidueKernel_of_isolatingRadius hr)
      (fun w hw => by
        simpa using differentiableAt_pascalCenteredXiLocalResidueKernel_of_isolatingRadius
          (z := z) hr ⟨hw.1.1, hw.1.2⟩)
      (tendsto_pascalCenteredXiLocalResidueKernel hz)
  rw [circleIntegral.integral_congr hr.1.le (fun w hw => ?_)]
  · simpa [smul_eq_mul] using hCauchy
  · have hwz : w ≠ z := by
      intro h
      subst w
      have : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hw
      exact hr.1.ne' this.symm
    simpa [smul_eq_mul] using
      (pascalCenteredXiNegLogDeriv_eq_inv_mul_localResidueKernel (z := z) hwz)

theorem circleIntegral_pascalCenteredXiNegLogDeriv_eq
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    circleIntegral pascalCenteredXiNegLogDeriv z
      (pascalCenteredXiIsolatingRadius z) =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ) :=
  circleIntegral_pascalCenteredXiNegLogDeriv_eq_of_isolatingRadius hz
    (pascalCenteredXiIsolatingRadius_spec hz)

theorem circleIntegral_pascalCenteredXiNegLogDeriv_sub_center_eq_riemannMultiplicity
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    circleIntegral pascalCenteredXiNegLogDeriv
      (ρ - criticalLineCenter)
      (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter)) =
      -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ) := by
  have hz : ρ - criticalLineCenter ∈ pascalCenteredXiZeros := by
    exact mem_pascalCenteredXiZeros.mpr
      (pascalCenteredRiemannXiKernel_sub_center_eq_zero_of_nontrivial hρ)
  rw [circleIntegral_pascalCenteredXiNegLogDeriv_eq hz]
  rw [pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity hρ]

/-- A fixed holomorphic weight times the centered Xi local residue kernel. -/
noncomputable def pascalCenteredXiWeightedLocalResidueKernel
    (h : ℂ → ℂ) (z w : ℂ) : ℂ :=
  h w * pascalCenteredXiLocalResidueKernel z w

theorem tendsto_pascalCenteredXiWeightedLocalResidueKernel
    {h : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeros)
    (hh : ContinuousAt h z) :
    Tendsto (pascalCenteredXiWeightedLocalResidueKernel h z) (𝓝[≠] z)
      (𝓝 (h z * (-(pascalCenteredXiZeroMultiplicity z : ℂ)))) := by
  exact hh.tendsto.mono_left nhdsWithin_le_nhds |>.mul
    (tendsto_pascalCenteredXiLocalResidueKernel hz)

theorem circleIntegral_weight_mul_pascalCenteredXiNegLogDeriv_eq_of_isolatingRadius
    {h : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeros)
    {r : ℝ} (hr : IsPascalCenteredXiIsolatingRadius z r)
    (hh : Differentiable ℂ h) :
    circleIntegral (fun w => h w * pascalCenteredXiNegLogDeriv w) z r =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ) * h z := by
  have hcont : ContinuousOn (pascalCenteredXiWeightedLocalResidueKernel h z)
      (Metric.closedBall z r \ {z}) := by
    intro w hw
    exact (hh w).continuousAt.continuousWithinAt.mul
      (continuousOn_pascalCenteredXiLocalResidueKernel_of_isolatingRadius hr w hw)
  have hdiff : ∀ w ∈ Metric.ball z r \ {z},
      DifferentiableAt ℂ (pascalCenteredXiWeightedLocalResidueKernel h z) w := by
    intro w hw
    exact (hh w).mul
      (differentiableAt_pascalCenteredXiLocalResidueKernel_of_isolatingRadius hr hw)
  have hCauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      (c := z) (R := r) hr.1 Set.countable_empty hcont
      (fun w hw => by simpa using hdiff w ⟨hw.1.1, hw.1.2⟩)
      (tendsto_pascalCenteredXiWeightedLocalResidueKernel hz (hh z).continuousAt)
  calc
    circleIntegral (fun w => h w * pascalCenteredXiNegLogDeriv w) z r =
        circleIntegral (fun w => (w - z)⁻¹ •
          pascalCenteredXiWeightedLocalResidueKernel h z w) z r := by
      rw [circleIntegral.integral_congr hr.1.le]
      intro w hw
      have hwz : w ≠ z := by
        intro hzw
        subst w
        have : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hw
        exact hr.1.ne' this.symm
      change h w * pascalCenteredXiNegLogDeriv w =
        (w - z)⁻¹ • pascalCenteredXiWeightedLocalResidueKernel h z w
      rw [pascalCenteredXiNegLogDeriv_eq_inv_mul_localResidueKernel (z := z) hwz]
      simp [pascalCenteredXiWeightedLocalResidueKernel, smul_eq_mul]
      ring
    _ = (2 * Real.pi * Complex.I) •
        (h z * (-(pascalCenteredXiZeroMultiplicity z : ℂ))) := hCauchy
    _ = -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ) * h z := by
      simp [smul_eq_mul]
      ring

theorem circleIntegral_weight_mul_pascalCenteredXiNegLogDeriv_eq
    {h : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeros)
    (hh : Differentiable ℂ h) :
    circleIntegral (fun w => h w * pascalCenteredXiNegLogDeriv w) z
      (pascalCenteredXiIsolatingRadius z) =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ) * h z :=
  circleIntegral_weight_mul_pascalCenteredXiNegLogDeriv_eq_of_isolatingRadius hz
    (pascalCenteredXiIsolatingRadius_spec hz) hh

/-! ## Fixed local charges in the finite PPW window -/

/-- The finite sum of independent centered Xi local circle charges. -/
noncomputable def pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral pascalCenteredXiNegLogDeriv
      (ρ - criticalLineCenter)
      (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter))

theorem pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass R =
      -(2 * Real.pi * Complex.I) *
        (pascalCriticalMirrorZeroWindowMultiplicity R : ℂ) := by
  classical
  change (∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
      circleIntegral pascalCenteredXiNegLogDeriv
        (ρ - criticalLineCenter)
        (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter))) =
    -(2 * Real.pi * Complex.I) *
      ↑(∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R, riemannZetaZeroMultiplicity ρ)
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρzero : NontrivialRiemannZetaZero ρ :=
    (mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2
  rw [circleIntegral_pascalCenteredXiNegLogDeriv_sub_center_eq_riemannMultiplicity hρzero]

theorem pascalCriticalMirrorZeroWindowNormalizedCenteredXiLocalContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass R =
      -(pascalCriticalMirrorZeroWindowMultiplicity R : ℂ) := by
  rw [pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass_eq]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

/-- The finite sum of fixed-weighted centered Xi local circle charges. -/
noncomputable def pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral
      (fun w => h w * pascalCenteredXiNegLogDeriv w)
      (ρ - criticalLineCenter)
      (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter))

theorem pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass h R =
      -(2 * Real.pi * Complex.I) *
        ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
          (riemannZetaZeroMultiplicity ρ : ℂ) * h (ρ - criticalLineCenter) := by
  classical
  change (∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
      circleIntegral
        (fun w => h w * pascalCenteredXiNegLogDeriv w)
        (ρ - criticalLineCenter)
        (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρzero : NontrivialRiemannZetaZero ρ :=
    (mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2
  have hz : ρ - criticalLineCenter ∈ pascalCenteredXiZeros := by
    exact mem_pascalCenteredXiZeros.mpr
      (pascalCenteredRiemannXiKernel_sub_center_eq_zero_of_nontrivial hρzero)
  have hlocal := circleIntegral_weight_mul_pascalCenteredXiNegLogDeriv_eq hz hh
  rw [pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity hρzero]
    at hlocal
  simpa only [mul_assoc] using hlocal

theorem pascalCriticalMirrorZeroWindowNormalizedCenteredXiWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass h R =
      -∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        (riemannZetaZeroMultiplicity ρ : ℂ) * h (ρ - criticalLineCenter) := by
  rw [pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass_eq hh]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

/-- The fixed holomorphic polynomial weight for the centered second moment. -/
noncomputable def pascalCenteredXiSecondWeight (z : ℂ) : ℂ := z ^ 2

theorem differentiable_pascalCenteredXiSecondWeight :
    Differentiable ℂ pascalCenteredXiSecondWeight := by
  unfold pascalCenteredXiSecondWeight
  fun_prop

/-- The fixed-weighted centered Xi local contour mass for the weight `z^2`. -/
noncomputable def pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass
    (R : ℝ) : ℂ :=
  pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass
    pascalCenteredXiSecondWeight R

theorem pascalCriticalMirrorZeroWindowNormalizedCenteredXiSecondLocalContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  simpa [pascalCenteredXiSecondWeight,
    pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass,
    pascalCriticalMirrorZeroWindowCenteredSecondMoment] using
    pascalCriticalMirrorZeroWindowNormalizedCenteredXiWeightedLocalContourMass_eq
      differentiable_pascalCenteredXiSecondWeight R

end DkMath.RH.CFBRCProjection
