/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
import DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

/-!
# Completed-zeta logarithmic-derivative decomposition

This module fixes the repository's completed-zeta normalization at the
factorized-kernel level and transports its negative logarithmic derivative to
ordinary zeta, the real Gamma factor, and the elementary factor `s * (1 - s)`.

The decomposition is local and hypothesis-driven.  In particular, it never
uses the totalized values of a quotient at a pole or zero as a substitute for
punctured-neighborhood regularity.  It also does not perform contour shifting,
prime summation, defect analysis, or an RH argument.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Repository-normalized factorization -/

/-- The factorized kernel used for local logarithmic-derivative transport. -/
noncomputable def pascalRiemannXiFactorizedKernel (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta s

/-- Away from `0` and the zeros of `Gammaℝ`, the pinned Mathlib identity for
ordinary zeta rewrites the completed zeta as `ζ * Gammaℝ`. -/
theorem completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hGamma : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- Near any point different from `0` and `1`, the pole-killed repository
kernel agrees with its completed-zeta factorization.

The equality is eventual at the neighborhood filter, so it can safely be
transported through `deriv`; a single pointwise equality is intentionally not
used as a derivative rewrite. -/
theorem pascalRiemannXiKernel_eventuallyEq_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    pascalRiemannXiKernel =ᶠ[𝓝 s]
      pascalRiemannXiFactorizedKernel := by
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with t ht0 ht1
  exact pascalRiemannXiKernel_eq_mul_completedRiemannZeta ht0 ht1

/-- Logarithmic derivatives are equal after the local factorization is
transported through eventual equality. -/
theorem pascalRiemannXiKernel_logDeriv_eq_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv pascalRiemannXiKernel s =
      logDeriv pascalRiemannXiFactorizedKernel s := by
  have hEq := pascalRiemannXiKernel_eventuallyEq_factorized hs0 hs1
  rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]

/-! ## Named decomposition terms -/

/-- The ordinary-zeta negative logarithmic derivative term. -/
noncomputable def pascalXiOrdinaryZetaNegLogDeriv (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- The archimedean correction retained as the negative logarithmic derivative
of Mathlib's `Complex.Gammaℝ` factor. -/
noncomputable def pascalXiArchimedeanLogDeriv (s : ℂ) : ℂ :=
  -logDeriv Complex.Gammaℝ s

/-- The elementary factor correction coming from `s * (1 - s)`. -/
noncomputable def pascalXiElementaryLogDerivCorrection (s : ℂ) : ℂ :=
  -1 / s + 1 / (1 - s)

private theorem differentiableAt_Gammaℝ_of_ne_zero
    {s : ℂ} (hGamma : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hi : DifferentiableAt ℂ (fun t : ℂ => (Complex.Gammaℝ t)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hii := hi.inv (inv_ne_zero hGamma)
  have hfun : (fun t : ℂ => ((Complex.Gammaℝ t)⁻¹)⁻¹) = Complex.Gammaℝ := by
    funext t
    simp only [inv_inv]
  rw [← hfun]
  exact hii

private theorem logDeriv_one_sub
    {s : ℂ} (_hs1 : s ≠ 1) :
    logDeriv (fun t : ℂ => 1 - t) s = -1 / (1 - s) := by
  rw [logDeriv_apply, deriv_const_sub_id]

/-- The uncentered negative logarithmic derivative decomposes into the
ordinary zeta, archimedean, and elementary terms. -/
theorem pascalRiemannXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    -logDeriv pascalRiemannXiKernel s =
      pascalXiOrdinaryZetaNegLogDeriv s +
        pascalXiArchimedeanLogDeriv s +
        pascalXiElementaryLogDerivCorrection s := by
  have hzf : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hgf : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_Gammaℝ_of_ne_zero hGamma
  have hsf : DifferentiableAt ℂ (fun t : ℂ => t) s := differentiableAt_id
  have h1sf : DifferentiableAt ℂ (fun t : ℂ => 1 - t) s :=
    (differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id
  have hGamma_event : ∀ᶠ t in 𝓝 s, Complex.Gammaℝ t ≠ 0 := by
    have hi_event : ∀ᶠ t in 𝓝 s, (Complex.Gammaℝ t)⁻¹ ≠ 0 :=
      (Complex.differentiable_Gammaℝ_inv.continuous.continuousAt).eventually_ne
        (inv_ne_zero hGamma)
    filter_upwards [hi_event] with t ht hzero
    exact ht (by simp [hzero])
  have hcompletedEq : completedRiemannZeta =ᶠ[𝓝 s]
      (fun t : ℂ => riemannZeta t * Complex.Gammaℝ t) := by
    filter_upwards [eventually_ne_nhds hs0, hGamma_event] with t ht0 htGamma
    exact completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero ht0 htGamma
  have hfactorizedEq : pascalRiemannXiFactorizedKernel =ᶠ[𝓝 s]
      (fun t : ℂ => t * (1 - t) * (riemannZeta t * Complex.Gammaℝ t)) := by
    filter_upwards [hcompletedEq] with t ht
    simp only [pascalRiemannXiFactorizedKernel]
    rw [ht]
  have hlogfactorized : logDeriv pascalRiemannXiFactorizedKernel s =
      logDeriv (fun t : ℂ => t * (1 - t) *
        (riemannZeta t * Complex.Gammaℝ t)) s := by
    rw [logDeriv_apply, logDeriv_apply, hfactorizedEq.deriv_eq,
      hfactorizedEq.eq_of_nhds]
  have hprod : logDeriv (fun t : ℂ => t * (1 - t) *
        (riemannZeta t * Complex.Gammaℝ t)) s =
      logDeriv (fun t : ℂ => t) s +
        logDeriv (fun t : ℂ => 1 - t) s +
        logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s := by
    rw [logDeriv_mul (f := fun t : ℂ => t * (1 - t))
      (g := fun t : ℂ => riemannZeta t * Complex.Gammaℝ t) s
      (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1)))
      (mul_ne_zero hzeta hGamma) (hsf.mul h1sf) (hzf.mul hgf),
      logDeriv_mul (f := fun t : ℂ => t) (g := fun t : ℂ => 1 - t) s
        hs0 (sub_ne_zero.mpr (Ne.symm hs1)) hsf h1sf,
      logDeriv_mul (f := riemannZeta) (g := Complex.Gammaℝ) s
        hzeta hGamma hzf hgf,
      logDeriv_one_sub hs1]
    ac_rfl
  rw [pascalRiemannXiKernel_logDeriv_eq_factorized hs0 hs1,
    hlogfactorized, hprod]
  simp only [pascalXiOrdinaryZetaNegLogDeriv, pascalXiArchimedeanLogDeriv,
    pascalXiElementaryLogDerivCorrection]
  simp only [logDeriv_apply]
  have hid : deriv (fun t : ℂ => t) s = 1 := by
    change deriv id s = 1
    exact deriv_id s
  have hsub : deriv (fun t : ℂ => 1 - t) s = -1 :=
    deriv_const_sub_id (1 : ℂ)
  rw [hid, hsub]
  field_simp [hs0, hs1, hzeta, hGamma]
  ring

/-! ## Centered coordinate transport -/

/-- The centered negative logarithmic derivative is the uncentered one at
`s = criticalLineCenter + z`.  The translation derivative is transported
explicitly; no informal change-of-variable is used. -/
theorem pascalCenteredXiNegLogDeriv_eq_uncentered
    (z : ℂ) :
    pascalCenteredXiNegLogDeriv z =
      -logDeriv pascalRiemannXiKernel (criticalLineCenter + z) := by
  unfold pascalCenteredXiNegLogDeriv pascalCenteredRiemannXiKernel
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_add]

/-- Centered-coordinate form of the completed-zeta logarithmic-derivative
decomposition. -/
theorem pascalCenteredXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary
    {z : ℂ}
    (hs0 : criticalLineCenter + z ≠ 0)
    (hs1 : criticalLineCenter + z ≠ 1)
    (hzeta : riemannZeta (criticalLineCenter + z) ≠ 0)
    (hGamma : Complex.Gammaℝ (criticalLineCenter + z) ≠ 0) :
    pascalCenteredXiNegLogDeriv z =
      pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z) +
        pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
        pascalXiElementaryLogDerivCorrection (criticalLineCenter + z) := by
  rw [pascalCenteredXiNegLogDeriv_eq_uncentered]
  exact pascalRiemannXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary
    hs0 hs1 hzeta hGamma

/-! ## Boundary safety contract -/

/-- A radius whose Xi contour is safe and whose ordinary factors are all
nonzero on the same centered sphere.

The extra factor hypotheses are intentional: Xi nonvanishing alone does not
license an individual zeta/Gamma contour term, because their singularities can
be cancelled by the factorized Xi kernel. -/
def IsPascalCenteredXiLogDerivDecompositionSafeRadius (R : ℝ) : Prop :=
  IsPascalCenteredXiBoundarySafeRadius R ∧
    ∀ z ∈ Metric.sphere (0 : ℂ) R,
      let s := criticalLineCenter + z
      s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ Complex.Gammaℝ s ≠ 0

/-- The stronger decomposition-safe radius implies the previously established
Xi boundary safety contract. -/
theorem isPascalCenteredXiLogDerivDecompositionSafeRadius_boundarySafe
    {R : ℝ} (hR : IsPascalCenteredXiLogDerivDecompositionSafeRadius R) :
    IsPascalCenteredXiBoundarySafeRadius R :=
  hR.1

/-! ## Weighted boundary decomposition -/

/-- On a decomposition-safe centered sphere, the weighted Xi logarithmic
derivative splits pointwise into ordinary-zeta, archimedean, and elementary
contributions.

This is an `EqOn` statement rather than a contour theorem: the individual
terms are not allowed to inherit regularity from a cancellation in the Xi
kernel. -/
theorem pascalCenteredXiWeightedNegLogDeriv_eq_decomposed_on_sphere
    {h : ℂ → ℂ} {R : ℝ}
    (hSafe : IsPascalCenteredXiLogDerivDecompositionSafeRadius R) :
    Set.EqOn
      (fun z => h z * pascalCenteredXiNegLogDeriv z)
      (fun z =>
        h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z) +
          h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
          h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z))
      (Metric.sphere (0 : ℂ) R) := by
  intro z hz
  rcases hSafe.2 z hz with ⟨hs0, hs1, hzeta, hGamma⟩
  change h z * pascalCenteredXiNegLogDeriv z = _
  rw [pascalCenteredXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary
    hs0 hs1 hzeta hGamma]
  ring

/-- Conditional contour-level split of the weighted outer integral.

The three `CircleIntegrable` hypotheses are explicit because the Xi-safe
contour does not by itself prove individual regularity of the decomposed
zeta/Gamma terms.  This theorem therefore records the exact remaining
XDP-009-facing contract without hiding singularities in circle-integral
totalization. -/
theorem pascalCenteredXiWeightedOuterContourMass_eq_decomposed
    {h : ℂ → ℂ} {R : ℝ}
    (hSafe : IsPascalCenteredXiLogDerivDecompositionSafeRadius R)
    (hzetaInt : CircleIntegrable
      (fun z => h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z)) 0 R)
    (hGammaInt : CircleIntegrable
      (fun z => h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z)) 0 R)
    (helemInt : CircleIntegrable
      (fun z => h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)) 0 R) :
    pascalCenteredXiWeightedOuterContourMass h R =
      circleIntegral
          (fun z => h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z)) 0 R +
        circleIntegral
          (fun z => h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z)) 0 R +
        circleIntegral
          (fun z => h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)) 0 R := by
  have hEq : Set.EqOn
      (fun z => h z * pascalCenteredXiNegLogDeriv z)
      (fun z =>
        h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z) +
          h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
          h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z))
      (Metric.sphere (0 : ℂ) R) := by
    intro z hz
    exact pascalCenteredXiWeightedNegLogDeriv_eq_decomposed_on_sphere hSafe hz
  unfold pascalCenteredXiWeightedOuterContourMass
  rw [circleIntegral.integral_congr hSafe.1.1.le hEq]
  rw [show (fun z =>
      h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z) +
        h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
        h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)) =
      (fun z =>
        h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z) +
          (h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
            h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z))) by
        funext z
        ring]
  have hsplit1 : circleIntegral
      (fun z =>
        h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z) +
          (h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
            h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z))) 0 R =
      circleIntegral
          (fun z => h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z)) 0 R +
        circleIntegral
          (fun z => h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
            h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)) 0 R := by
    simpa only [Pi.add_apply] using
      (circleIntegral.integral_add hzetaInt (hGammaInt.add helemInt))
  have hsplit2 : circleIntegral
      (fun z => h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z) +
        h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)) 0 R =
      circleIntegral
          (fun z => h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z)) 0 R +
        circleIntegral
          (fun z => h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)) 0 R := by
    simpa only [Pi.add_apply] using
      (circleIntegral.integral_add hGammaInt helemInt)
  rw [hsplit1, hsplit2]
  ring

/-! ## Existing prime-side endpoint hook -/

/-- The ordinary-zeta term is definitionally the target of the existing
von-Mangoldt finite-cutoff endpoint on `1 < s.re`.  No L-series convergence
argument is reproved here. -/
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun X => pascalPrimePowerPHZFiniteUpTo X s) atTop
      (nhds (pascalXiOrdinaryZetaNegLogDeriv s)) := by
  simpa [pascalXiOrdinaryZetaNegLogDeriv] using
    tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div hs

end DkMath.RH.CFBRCProjection
