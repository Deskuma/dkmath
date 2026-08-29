/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerModeProjection
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaMirrorGapBeamProjection"

/-!
# CFZP-002: mirror Gap analytic Beam

For one real mirror mode, the amplitude difference has a regularized
divided-difference factorization

`L_q δ - R_q δ = δ * amplitudeDifferenceBeam q δ`.

Squaring this identity projects the cosmic coordinate Gap `δ^2` to the
existing prime-mirror amplitude Gap.  The value at the center is chosen from
the derivative, and its regularity is proved directly from the derivative
and slope APIs.

This module remains at the finite real-amplitude, single-mode level.  It does
not introduce phases, infinite products, zeta zeros, Mellin integrals, or
rectangle source identities.
-/

noncomputable section

open scoped Topology
open Filter TopologicalSpace

namespace DkMath.RH.CFBRCProjection

/-- The source difference of the two real prime-mirror amplitudes. -/
noncomputable def cfzpMirrorAmplitudeDifference (q : ℕ) (δ : ℝ) : ℝ :=
  primeMirrorLeftAmplitude q δ - primeMirrorRightAmplitude q δ

/-- The derivative-compatible regularized divided-difference Beam. -/
noncomputable def cfzpMirrorAmplitudeDifferenceBeam (q : ℕ) (δ : ℝ) : ℝ :=
  if δ = 0 then
    -2 * Real.log (q : ℝ)
  else
    cfzpMirrorAmplitudeDifference q δ / δ

/-- The squared Beam carrying the prime-mirror Gap. -/
noncomputable def cfzpMirrorGapBeam (q : ℕ) (δ : ℝ) : ℝ :=
  (cfzpMirrorAmplitudeDifferenceBeam q δ) ^ 2

/-! ## Source and center values -/

@[simp] theorem cfzpMirrorAmplitudeDifference_eq
    (q : ℕ) (δ : ℝ) :
    cfzpMirrorAmplitudeDifference q δ =
      primeMirrorLeftAmplitude q δ - primeMirrorRightAmplitude q δ := by
  rfl

@[simp] theorem cfzpMirrorAmplitudeDifferenceBeam_zero (q : ℕ) :
    cfzpMirrorAmplitudeDifferenceBeam q 0 =
      -2 * Real.log (q : ℝ) := by
  simp [cfzpMirrorAmplitudeDifferenceBeam]

@[simp] theorem cfzpMirrorGapBeam_zero (q : ℕ) :
    cfzpMirrorGapBeam q 0 =
      4 * (Real.log (q : ℝ)) ^ 2 := by
  rw [cfzpMirrorGapBeam, cfzpMirrorAmplitudeDifferenceBeam_zero]
  ring

/-! ## Exact first-order and squared factorizations -/

theorem cfzpMirrorAmplitudeDifference_eq_delta_mul_beam
    (q : ℕ) (δ : ℝ) :
    cfzpMirrorAmplitudeDifference q δ =
      δ * cfzpMirrorAmplitudeDifferenceBeam q δ := by
  by_cases hδ : δ = 0
  · subst δ
    simp [cfzpMirrorAmplitudeDifference, cfzpMirrorAmplitudeDifferenceBeam,
      primeMirrorLeftAmplitude, primeMirrorRightAmplitude]
  · rw [cfzpMirrorAmplitudeDifferenceBeam, ite_eq_right hδ]
    field_simp

theorem primeMirrorOffsetGap_eq_delta_sq_mul_cfzpMirrorGapBeam
    (q : ℕ) (δ : ℝ) :
    primeMirrorOffsetGap q δ =
      δ ^ 2 * cfzpMirrorGapBeam q δ := by
  change (cfzpMirrorAmplitudeDifference q δ) ^ 2 =
    δ ^ 2 * (cfzpMirrorAmplitudeDifferenceBeam q δ) ^ 2
  rw [cfzpMirrorAmplitudeDifference_eq_delta_mul_beam]
  ring

theorem primeMirrorOffsetGapAt_eq_centeredSigma_sq_mul_cfzpMirrorGapBeam
    (q : ℕ) (s : ℂ) :
    primeMirrorOffsetGapAt q s =
      (centeredSigma s.re) ^ 2 *
        cfzpMirrorGapBeam q (centeredSigma s.re) := by
  unfold primeMirrorOffsetGapAt
  exact primeMirrorOffsetGap_eq_delta_sq_mul_cfzpMirrorGapBeam
    q (centeredSigma s.re)

/-! ## Derivative and regularity at the center -/

theorem tendsto_cfzpMirrorAmplitudeDifferenceBeam_zero
    (q : ℕ) :
    Tendsto
      (cfzpMirrorAmplitudeDifferenceBeam q)
      (nhds 0)
      (nhds (-2 * Real.log (q : ℝ))) := by
  have hleftArg :
      HasDerivAt (fun δ : ℝ => -δ * Real.log (q : ℝ))
        (-Real.log (q : ℝ)) 0 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).neg.mul_const
        (Real.log (q : ℝ)))
  have hrightArg :
      HasDerivAt (fun δ : ℝ => δ * Real.log (q : ℝ))
        (Real.log (q : ℝ)) 0 :=
    hasDerivAt_mul_const (Real.log (q : ℝ))
  have hleft :=
    (Real.hasDerivAt_exp ((fun δ : ℝ => -δ * Real.log (q : ℝ)) 0)).comp
      0 hleftArg
  have hright :=
    (Real.hasDerivAt_exp ((fun δ : ℝ => δ * Real.log (q : ℝ)) 0)).comp
      0 hrightArg
  have hleft' :
      HasDerivAt (fun δ : ℝ => Real.exp (-δ * Real.log (q : ℝ)))
        (-Real.log (q : ℝ)) 0 := by
    simpa only [Function.comp_def, Real.exp_zero, zero_mul, neg_zero, one_mul]
      using hleft
  have hright' :
      HasDerivAt (fun δ : ℝ => Real.exp (δ * Real.log (q : ℝ)))
        (Real.log (q : ℝ)) 0 := by
    simpa only [Function.comp_def, Real.exp_zero, zero_mul, one_mul] using hright
  have hdiff := hleft'.sub hright'
  have hslope :=
    hdiff.tendsto_slope_zero
  have hslope' :
    Tendsto
        (fun t : ℝ => t⁻¹ *
          (Real.exp (-t * Real.log (q : ℝ)) -
            Real.exp (t * Real.log (q : ℝ))))
        (𝓝[≠] 0) (nhds (-2 * Real.log (q : ℝ))) := by
    rw [show -2 * Real.log (q : ℝ) =
      -Real.log (q : ℝ) - Real.log (q : ℝ) by ring]
    simpa only [smul_eq_mul, add_zero, zero_add, sub_zero, Pi.sub_apply,
      Real.exp_zero, zero_mul, neg_zero, one_mul, sub_self] using hslope
  have hzero : cfzpMirrorAmplitudeDifference q 0 = 0 := by
    simp [cfzpMirrorAmplitudeDifference, primeMirrorLeftAmplitude,
      primeMirrorRightAmplitude]
  have hzero' :
      primeMirrorLeftAmplitude q 0 - primeMirrorRightAmplitude q 0 = 0 := by
    simp [primeMirrorLeftAmplitude, primeMirrorRightAmplitude]
  have hpunct :
      Tendsto
        (fun δ : ℝ => cfzpMirrorAmplitudeDifference q δ / δ)
        (𝓝[≠] 0)
        (nhds (-2 * Real.log (q : ℝ))) := by
    simpa [primeMirrorLeftAmplitude, primeMirrorRightAmplitude,
      div_eq_mul_inv, smul_eq_mul, hzero, hzero', mul_comm] using hslope'
  have hbeam_punct :
      Tendsto (cfzpMirrorAmplitudeDifferenceBeam q)
        (𝓝[≠] 0) (nhds (-2 * Real.log (q : ℝ))) := by
    apply hpunct.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : δ ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hδ
    rw [cfzpMirrorAmplitudeDifferenceBeam, ite_eq_right hδ']
  rw [← nhdsNE_sup_pure 0]
  refine hbeam_punct.sup ?_
  have hpure :
      Tendsto (cfzpMirrorAmplitudeDifferenceBeam q) (pure 0)
        (nhds (cfzpMirrorAmplitudeDifferenceBeam q 0)) :=
    tendsto_pure_nhds _ _
  simpa only [cfzpMirrorAmplitudeDifferenceBeam_zero] using hpure

theorem continuousAt_cfzpMirrorAmplitudeDifferenceBeam_zero
    (q : ℕ) :
    ContinuousAt (cfzpMirrorAmplitudeDifferenceBeam q) 0 := by
  rw [ContinuousAt]
  simpa only [cfzpMirrorAmplitudeDifferenceBeam_zero] using
    tendsto_cfzpMirrorAmplitudeDifferenceBeam_zero q

theorem tendsto_cfzpMirrorGapBeam_zero (q : ℕ) :
    Tendsto
      (cfzpMirrorGapBeam q)
      (nhds 0)
      (nhds (4 * (Real.log (q : ℝ)) ^ 2)) := by
  have hbeam := tendsto_cfzpMirrorAmplitudeDifferenceBeam_zero q
  have hsq := hbeam.mul hbeam
  change Tendsto
    (fun δ : ℝ => (cfzpMirrorAmplitudeDifferenceBeam q δ) ^ 2)
    (nhds 0) (nhds (4 * (Real.log (q : ℝ)) ^ 2))
  rw [show 4 * (Real.log (q : ℝ)) ^ 2 =
      (-2 * Real.log (q : ℝ)) * (-2 * Real.log (q : ℝ)) by ring]
  simpa only [Pi.pow_apply, pow_two] using hsq

/-! ## Noncollapse at the critical center -/

theorem cfzpMirrorGapBeam_zero_pos
    {q : ℕ} (hq : 1 < q) :
    0 < cfzpMirrorGapBeam q 0 := by
  rw [cfzpMirrorGapBeam_zero]
  have hlog : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hq
  positivity

end DkMath.RH.CFBRCProjection
