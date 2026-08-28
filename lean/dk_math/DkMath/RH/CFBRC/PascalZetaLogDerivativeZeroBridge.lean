/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalZetaLogDerivativeZeroBridge"

/-!
# The Pascal prime-power limit and the meromorphic zeta log derivative

PPW-012 records the zero-side local structure of the PPW-011 limit.  Pole
information is expressed by punctured-neighborhood limits, never by the
totalized value of division at a zero.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped ComplexConjugate

/-- The meromorphic target of the finite Pascal prime-power cutoff. -/
noncomputable def pascalZetaNegLogDeriv (s : ℂ) : ℂ :=
  - logDeriv riemannZeta s

@[simp] theorem pascalZetaNegLogDeriv_eq_neg_deriv_div (s : ℂ) :
    pascalZetaNegLogDeriv s = - deriv riemannZeta s / riemannZeta s := by
  simp [pascalZetaNegLogDeriv, logDeriv_apply]
  ring

/-- PPW-011's safe-half-plane limit expressed through the named meromorphic target. -/
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_pascalZetaNegLogDeriv
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun X => pascalPrimePowerPHZFiniteUpTo X s) atTop
      (nhds (pascalZetaNegLogDeriv s)) := by
  simpa only [pascalZetaNegLogDeriv_eq_neg_deriv_div] using
    tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div hs

/-- Away from its pole at one, the negative zeta log derivative is meromorphic. -/
theorem meromorphicOn_pascalZetaNegLogDeriv :
    MeromorphicOn pascalZetaNegLogDeriv ({1}ᶜ : Set ℂ) := by
  have hz : MeromorphicOn riemannZeta ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.meromorphicOn
  change MeromorphicOn (fun s => - logDeriv riemannZeta s) ({1}ᶜ : Set ℂ)
  exact hz.logDeriv.fun_neg

/-- A Riemann-zeta zero is not the exceptional point one. -/
theorem ne_one_of_mem_riemannZetaZeros
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) : ρ ≠ 1 := by
  intro h
  apply riemannZeta_one_ne_zero
  rw [← h]
  exact mem_riemannZetaZeros.mp hρ

/-- Zeta is analytic at each of its zeros. -/
theorem analyticAt_riemannZeta_of_mem_riemannZetaZeros
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    AnalyticAt ℂ riemannZeta ρ := by
  exact analyticOn_riemannZeta ρ (by simpa using ne_one_of_mem_riemannZetaZeros hρ)

/-- At a simple zeta zero, the negative log derivative has residue signature `-1`. -/
theorem tendsto_mul_pascalZetaNegLogDeriv_simpleZero
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros)
    (hρsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun w => (w - ρ) * pascalZetaNegLogDeriv w)
      (nhdsWithin ρ {ρ}ᶜ) (nhds (-1)) := by
  have hzero : riemannZeta ρ = 0 := mem_riemannZetaZeros.mp hρ
  have hlim := AnalyticAt.tendsto_mul_logDeriv_simple_zero
    (analyticAt_riemannZeta_of_mem_riemannZetaZeros hρ) hzero hρsimple
  simpa [pascalZetaNegLogDeriv, mul_neg, neg_one_mul] using hlim.neg

/-- The zeta-zero set is closed under complex conjugation. -/
theorem mem_riemannZetaZeros_conj_iff {s : ℂ} :
    conj s ∈ riemannZetaZeros ↔ s ∈ riemannZetaZeros := by
  rw [mem_riemannZetaZeros, mem_riemannZetaZeros, riemannZeta_conj]
  simp

/-- Compact windows contain only finitely many Riemann-zeta zeros. -/
theorem finite_riemannZetaZeros_in_compact
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ riemannZetaZeros).Finite :=
  hK.inter_riemannZetaZeros_finite

end DkMath.RH.CFBRCProjection
