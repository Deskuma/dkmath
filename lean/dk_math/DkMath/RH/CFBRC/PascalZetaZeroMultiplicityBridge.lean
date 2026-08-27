/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge"

/-!
# Zeta zero multiplicities and local logarithmic derivatives

This module fixes `analyticOrderNatAt` as the theorem-facing zeta-zero
multiplicity, after proving its analytic order is finite.  It then transports
the exact local analytic factorization through `logDeriv`, giving the
punctured logarithmic-derivative residue at an arbitrary (not necessarily
simple) zeta zero.  A local circle-integral formula is deliberately not
asserted here: the project currently has no specified contour convention
(orientation, parametrization, or normalization) against which such a
formula could be stated without changing its mathematical content.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- The finite analytic order of a Riemann-zeta zero. -/
noncomputable def riemannZetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ

/-- Zeta has finite analytic order at every zero, since it is nonzero at `2` on its
connected analytic domain `{1}ᶜ`. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_mem_riemannZetaZeros
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  apply AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    analyticOn_riemannZeta
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (x := (2 : ℂ))
  · norm_num
  · simpa using ne_one_of_mem_riemannZetaZeros hρ
  · have horder : analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr
        (riemannZeta_ne_zero_of_one_le_re (by norm_num)))
    exact horder.trans_ne ENat.zero_ne_top

@[simp] theorem analyticOrderAt_riemannZeta_eq_multiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    analyticOrderAt riemannZeta ρ = (riemannZetaZeroMultiplicity ρ : ℕ∞) := by
  symm
  exact Nat.cast_analyticOrderNatAt
    (analyticOrderAt_riemannZeta_ne_top_of_mem_riemannZetaZeros hρ)

theorem riemannZetaZeroMultiplicity_pos
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    0 < riemannZetaZeroMultiplicity ρ := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hzero : analyticOrderAt riemannZeta ρ = 0 := by
    rw [analyticOrderAt_riemannZeta_eq_multiplicity hρ, hm]
    rfl
  exact (analyticAt_riemannZeta_of_mem_riemannZetaZeros hρ).analyticOrderAt_ne_zero.mpr
    (mem_riemannZetaZeros.mp hρ) hzero

/-- The exact finite-order local factorization of zeta at an arbitrary zero. -/
theorem exists_riemannZeta_local_factorization
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
      g ρ ≠ 0 ∧
      riemannZeta =ᶠ[nhds ρ]
        (fun w => (w - ρ) ^ riemannZetaZeroMultiplicity ρ * g w) := by
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    (analyticAt_riemannZeta_of_mem_riemannZetaZeros hρ).analyticOrderAt_ne_top.mp
      (analyticOrderAt_riemannZeta_ne_top_of_mem_riemannZetaZeros hρ)
  refine ⟨g, hg, hg0, ?_⟩
  simpa [riemannZetaZeroMultiplicity, smul_eq_mul] using hfactor

/-- At a zeta zero, the punctured negative logarithmic derivative has residue
the negative of the analytic multiplicity. -/
theorem tendsto_mul_pascalZetaNegLogDeriv_zeroMultiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    Tendsto
      (fun w => (w - ρ) * pascalZetaNegLogDeriv w)
      (𝓝[≠] ρ)
      (𝓝 (-(riemannZetaZeroMultiplicity ρ : ℂ))) := by
  obtain ⟨g, hg, hg0, hfactor⟩ := exists_riemannZeta_local_factorization hρ
  let m : ℕ := riemannZetaZeroMultiplicity ρ
  have hmpos : 0 < m := by
    simpa [m] using riemannZetaZeroMultiplicity_pos hρ
  have hfactor' : riemannZeta =ᶠ[𝓝[≠] ρ]
      (fun w => (w - ρ) ^ m * g w) := by
    simpa [m] using hfactor.filter_mono nhdsWithin_le_nhds
  have hg_ne : ∀ᶠ w in 𝓝[≠] ρ, g w ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hg_analytic : ∀ᶠ w in 𝓝[≠] ρ, AnalyticAt ℂ g w :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog : logDeriv riemannZeta =ᶠ[𝓝[≠] ρ]
      logDeriv (fun w => (w - ρ) ^ m * g w) :=
    hfactor'.nhdsNE_deriv.div hfactor'
  have hlogg : Tendsto (logDeriv g) (𝓝[≠] ρ) (𝓝 (logDeriv g ρ)) := by
    change Tendsto (deriv g / g) (𝓝[≠] ρ) (𝓝 (deriv g ρ / g ρ))
    exact (hg.deriv.continuousAt.tendsto.div hg.continuousAt.tendsto hg0).mono_left
      nhdsWithin_le_nhds
  have hsub : Tendsto (fun w : ℂ => w - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    convert
      ((tendsto_id.sub tendsto_const_nhds :
        Tendsto (fun w : ℂ => w - ρ) (𝓝 ρ) (𝓝 (ρ - ρ))).mono_left nhdsWithin_le_nhds) using 1 <;>
      simp
  have hregular : Tendsto (fun w => (w - ρ) * logDeriv g w)
      (𝓝[≠] ρ) (𝓝 0) := by
    simpa using hsub.mul hlogg
  have hmodel : Tendsto
      (fun w => (w - ρ) * (-logDeriv (fun z => (z - ρ) ^ m * g z) w))
      (𝓝[≠] ρ) (𝓝 (-(m : ℂ))) := by
    have hEq : (fun w => (w - ρ) * (-logDeriv (fun z => (z - ρ) ^ m * g z) w))
        =ᶠ[𝓝[≠] ρ] (fun w => -(m : ℂ) - (w - ρ) * logDeriv g w) := by
      filter_upwards [hg_ne, hg_analytic, self_mem_nhdsWithin] with w hw hgw hwρmem
      have hwρ : w - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hwρmem)
      rw [logDeriv_mul (f := fun z : ℂ => (z - ρ) ^ m) (g := g) w
        (show (w - ρ) ^ m ≠ 0 from pow_ne_zero m hwρ) hw
        (by fun_prop) hgw.differentiableAt]
      have hderiv : deriv (fun z : ℂ => (z - ρ) ^ m) w =
          (m : ℂ) * (w - ρ) ^ (m - 1) := by
        convert (((hasDerivAt_id w).sub_const ρ).pow m).deriv using 1 <;> simp
      have hpow : (w - ρ) ^ m = (w - ρ) ^ (m - 1) * (w - ρ) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmpos)]
      simp only [logDeriv_apply, hderiv]
      rw [hpow]
      field_simp
      ring
    refine (show Tendsto (fun w => -(m : ℂ) - (w - ρ) * logDeriv g w)
      (𝓝[≠] ρ) (𝓝 (-(m : ℂ))) by simpa using tendsto_const_nhds.sub hregular).congr' ?_
    exact hEq.symm
  refine hmodel.congr' ?_
  filter_upwards [hlog] with w hw
  simp only [pascalZetaNegLogDeriv, hw]

/-- The multiplicity count in a finite critical-mirror zero window. -/
noncomputable def pascalCriticalMirrorZeroWindowMultiplicity (R : ℝ) : ℕ :=
  (pascalCriticalMirrorZeroWindowFinset R).sum riemannZetaZeroMultiplicity

theorem pascalCriticalMirrorZeroWindowMultiplicity_pos_of_nonempty
    {R : ℝ} (hW : (pascalCriticalMirrorZeroWindowFinset R).Nonempty) :
    0 < pascalCriticalMirrorZeroWindowMultiplicity R := by
  rcases hW with ⟨ρ, hρ⟩
  have hρzero : ρ ∈ riemannZetaZeros :=
    nontrivialRiemannZetaZero_mem_riemannZetaZeros
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2)
  exact lt_of_lt_of_le (riemannZetaZeroMultiplicity_pos hρzero)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ)

end DkMath.RH.CFBRCProjection
