/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
import DkMath.RH.CFBRC.ZeroDerivedDualEndpointPositiveScalarCoercivityAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.ZeroDerivedDualTailRateNormalizedModeBridgeAudit"

/-!
# ZDSS-004: dual-tail rate extraction and normalized-mode bridge audit

The ordinary paired-Eta tail has an unconditional nonzero asymptotic after
multiplication by its natural index power and a unit pair-frame rotation.  At
a nonreal standard zeta zero, the exact identity `partial = -tail` transports
that asymptotic separately to the original and critical-mirror finite
partials.  This gives genuine zero-derived two-sided endpoint rate data.

The rate data does not bound the normalized increment Gap.  The raw ratio of
the two endpoint-partial norms factors exactly as the increment-mode ratio
times a self-normalized endpoint ratio.  The latter tends to a finite positive
constant, while the former mode ratio retains the off-critical index power.
Consequently the two nonzero endpoint rate limits are compatible with the
existing off-critical normalized-Gap divergence theorem.  No bounded-Gap,
no-cancellation, or RH-equivalent provider is assumed here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-! ## Zero-derived normalized endpoint rates -/

/--
The paired-Eta finite partial at `k + 1`, normalized by its natural index
power and transported into the same unit pair-left frame as the tail theorem.
-/
noncomputable def etaPairIndexNormalizedRotatedPartial
    (z : ℂ) (k : ℕ) : ℂ :=
  (((((k + 1 : ℕ) : ℝ)) ^ z.re : ℝ) : ℂ) *
    (etaPairBaseRotation z k * etaPairedPartial (k + 1) z)

/-- Gauge-invariant norm of the naturally normalized finite partial. -/
noncomputable def etaPairIndexNormalizedPartialNorm
    (z : ℂ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ z.re) *
    ‖etaPairedPartial (k + 1) z‖

/--
At a nonreal standard zero, the normalized finite partial is exactly the
negative normalized tail at every index.
-/
theorem etaPairIndexNormalizedRotatedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    {z : ℂ} (hz : NontrivialRiemannZetaZero z) (hzim : z.im ≠ 0)
    (k : ℕ) :
    etaPairIndexNormalizedRotatedPartial z k =
      -etaPairIndexNormalizedRotatedTail z k := by
  unfold etaPairIndexNormalizedRotatedPartial
    etaPairIndexNormalizedRotatedTail
  rw [etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
    hz hzim (k + 1)]
  ring

/--
The normalized rotated finite partial at a nonreal standard zero converges to
the negative explicit Euler half-tail constant.  The normalization theorem
itself is unconditional; the zero hypothesis is used only for
`etaPairedPartial = -etaPairTail`.
-/
theorem etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero
    {z : ℂ} (hz : NontrivialRiemannZetaZero z) (hzim : z.im ≠ 0) :
    Tendsto (etaPairIndexNormalizedRotatedPartial z) atTop
      (nhds (-etaPairIndexNormalizedTailConstant z)) := by
  have htail :=
    (etaPairIndexNormalizedRotatedTail_tendsto_constant
      (nontrivialRiemannZetaZero_re_pos hz)).neg
  refine htail.congr' (Eventually.of_forall fun k => ?_)
  exact
    (etaPairIndexNormalizedRotatedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hz hzim k).symm

/-- Pair-frame rotation does not change the normalized finite-partial norm. -/
theorem norm_etaPairIndexNormalizedRotatedPartial
    (z : ℂ) (k : ℕ) :
    ‖etaPairIndexNormalizedRotatedPartial z k‖ =
      etaPairIndexNormalizedPartialNorm z k := by
  unfold etaPairIndexNormalizedRotatedPartial
    etaPairIndexNormalizedPartialNorm
  rw [norm_mul, norm_mul, norm_etaPairBaseRotation, one_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/--
The gauge-invariant normalized partial norm has a finite nonzero limit at a
nonreal standard zero.  This is the two-sided endpoint rate extracted from the
zero-derived tail identity.
-/
theorem etaPairIndexNormalizedPartialNorm_tendsto_constantNorm_of_nontrivialRiemannZetaZero
    {z : ℂ} (hz : NontrivialRiemannZetaZero z) (hzim : z.im ≠ 0) :
    Tendsto (etaPairIndexNormalizedPartialNorm z) atTop
      (nhds ‖etaPairIndexNormalizedTailConstant z‖) := by
  have hpartial :=
    etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero
      hz hzim
  have hnorm :=
    (continuous_norm.tendsto
      (-etaPairIndexNormalizedTailConstant z)).comp hpartial
  have hnorm' :
      Tendsto
        (fun k : ℕ => ‖etaPairIndexNormalizedRotatedPartial z k‖)
        atTop (nhds ‖etaPairIndexNormalizedTailConstant z‖) := by
    change Tendsto
      (fun k : ℕ => ‖etaPairIndexNormalizedRotatedPartial z k‖)
      atTop (nhds ‖-etaPairIndexNormalizedTailConstant z‖) at hnorm
    simpa only [Function.comp_apply, norm_neg] using hnorm
  refine hnorm'.congr' (Eventually.of_forall fun k => ?_)
  exact norm_etaPairIndexNormalizedRotatedPartial z k

/-- The explicit normalized-tail constant used by the rate theorem is nonzero. -/
private theorem etaPairIndexNormalizedTailConstant_ne_zero_zdss004
    (z : ℂ) :
    etaPairIndexNormalizedTailConstant z ≠ 0 := by
  unfold etaPairIndexNormalizedTailConstant
  apply mul_ne_zero
  · norm_num
  · exact_mod_cast
      (Real.rpow_pos_of_pos (by norm_num : 0 < (1 : ℝ) / 2) z.re).ne'

/--
Certificate collecting the two separate nonzero normalized endpoint rates.
It records U1 information only and contains no mode-Gap boundedness field.
-/
structure EtaDualEndpointNormalizedRateCertificate (s : ℂ) : Prop where
  original_rate :
    Tendsto (etaPairIndexNormalizedRotatedPartial s) atTop
      (nhds (-etaPairIndexNormalizedTailConstant s))
  mirror_rate :
    Tendsto (etaPairIndexNormalizedRotatedPartial (criticalMirror s)) atTop
      (nhds (-etaPairIndexNormalizedTailConstant (criticalMirror s)))
  original_limit_ne_zero :
    -etaPairIndexNormalizedTailConstant s ≠ 0
  mirror_limit_ne_zero :
    -etaPairIndexNormalizedTailConstant (criticalMirror s) ≠ 0

/-- Build both endpoint rate certificates from the standard zero hypothesis. -/
theorem etaDualEndpointNormalizedRateCertificate_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaDualEndpointNormalizedRateCertificate s := by
  have himMirror : (criticalMirror s).im ≠ 0 := by
    simpa using him
  exact
    { original_rate :=
        etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero
          hs him
      mirror_rate :=
        etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero
          (criticalMirror_nontrivialRiemannZetaZero hs) himMirror
      original_limit_ne_zero :=
        neg_ne_zero.mpr (etaPairIndexNormalizedTailConstant_ne_zero_zdss004 s)
      mirror_limit_ne_zero :=
        neg_ne_zero.mpr
          (etaPairIndexNormalizedTailConstant_ne_zero_zdss004
            (criticalMirror s)) }

/-! ## Endpoint-rate ratio and the exact mode-ratio factor -/

/-- Ratio after normalizing each endpoint by its own natural decay exponent. -/
noncomputable def etaDualEndpointNormalizedNormRatio
    (k : ℕ) (s : ℂ) : ℝ :=
  etaPairIndexNormalizedPartialNorm (criticalMirror s) k /
    etaPairIndexNormalizedPartialNorm s k

/-- Finite positive limit of the separately normalized endpoint-norm ratio. -/
noncomputable def etaDualEndpointNormalizedNormRatioLimit (s : ℂ) : ℝ :=
  ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖ /
    ‖etaPairIndexNormalizedTailConstant s‖

/-- Raw ratio of the mirror and original paired-partial norms at pair count `k+1`. -/
noncomputable def etaDualEndpointRawNormRatio
    (k : ℕ) (s : ℂ) : ℝ :=
  ‖etaPairedPartial (k + 1) (criticalMirror s)‖ /
    ‖etaPairedPartial (k + 1) s‖

/--
At a nonreal standard zero, the separately normalized endpoint-norm ratio
converges to an explicit finite constant.
-/
theorem etaDualEndpointNormalizedNormRatio_tendsto_limit_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun k : ℕ => etaDualEndpointNormalizedNormRatio k s)
      atTop (nhds (etaDualEndpointNormalizedNormRatioLimit s)) := by
  have himMirror : (criticalMirror s).im ≠ 0 := by
    simpa using him
  have horiginal :=
    etaPairIndexNormalizedPartialNorm_tendsto_constantNorm_of_nontrivialRiemannZetaZero
      hs him
  have hmirror :=
    etaPairIndexNormalizedPartialNorm_tendsto_constantNorm_of_nontrivialRiemannZetaZero
      (criticalMirror_nontrivialRiemannZetaZero hs) himMirror
  have horiginalLimit : ‖etaPairIndexNormalizedTailConstant s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (etaPairIndexNormalizedTailConstant_ne_zero_zdss004 s)
  have hquot := hmirror.div horiginal horiginalLimit
  change Tendsto
    (fun k : ℕ =>
      etaPairIndexNormalizedPartialNorm (criticalMirror s) k /
        etaPairIndexNormalizedPartialNorm s k)
    atTop
    (nhds (‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖ /
      ‖etaPairIndexNormalizedTailConstant s‖)) at hquot
  simpa [etaDualEndpointNormalizedNormRatio,
    etaDualEndpointNormalizedNormRatioLimit] using hquot

/-- The limit of the separately normalized endpoint-norm ratio is positive. -/
theorem etaDualEndpointNormalizedNormRatioLimit_pos (s : ℂ) :
    0 < etaDualEndpointNormalizedNormRatioLimit s := by
  unfold etaDualEndpointNormalizedNormRatioLimit
  exact div_pos
    (norm_pos_iff.mpr
      (etaPairIndexNormalizedTailConstant_ne_zero_zdss004
        (criticalMirror s)))
    (norm_pos_iff.mpr
      (etaPairIndexNormalizedTailConstant_ne_zero_zdss004 s))

/--
Exact source/mode ratio bridge.  Before taking limits, the raw endpoint norm
ratio is the increment-mode ratio times the ratio obtained after normalizing
each whole endpoint by its own exponent.  This identity exposes, rather than
removes, the off-critical index power.
-/
theorem etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio
    (k : ℕ) (s : ℂ)
    (horiginal : etaPairedPartial (k + 1) s ≠ 0) :
    etaDualEndpointRawNormRatio k s =
      etaEndpointIncrementMirrorRatio s k *
        etaDualEndpointNormalizedNormRatio k s := by
  have hbase : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hscaleOriginal :
      (((k + 1 : ℕ) : ℝ) ^ s.re) ≠ 0 :=
    (Real.rpow_pos_of_pos hbase _).ne'
  have hscaleMirror :
      (((k + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) ≠ 0 :=
    (Real.rpow_pos_of_pos hbase _).ne'
  have hnormOriginal : ‖etaPairedPartial (k + 1) s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr horiginal
  have hpower :
      (((k + 1 : ℕ) : ℝ) ^ (2 * centeredSigma s.re)) *
          (((k + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) =
        (((k + 1 : ℕ) : ℝ) ^ s.re) := by
    rw [← Real.rpow_add hbase]
    congr 1
    rw [criticalMirror_re]
    unfold centeredSigma
    ring
  unfold etaDualEndpointRawNormRatio
    etaDualEndpointNormalizedNormRatio
    etaPairIndexNormalizedPartialNorm
  rw [etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio,
    etaMirrorAmplitudeRatio_eq_rpow]
  field_simp [hnormOriginal, hscaleOriginal, hscaleMirror]
  rw [← hpower]
  ring

/--
At a nonreal standard zero, the exact source/mode ratio bridge holds for all
sufficiently large indices; eventual nonvanishing follows from the nonzero
normalized endpoint limit rather than from an assumed monotonicity theorem.
-/
theorem eventually_etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      etaDualEndpointRawNormRatio k s =
        etaEndpointIncrementMirrorRatio s k *
          etaDualEndpointNormalizedNormRatio k s := by
  have hpartial :=
    etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero
      hs him
  have hlimitNe : -etaPairIndexNormalizedTailConstant s ≠ 0 :=
    neg_ne_zero.mpr (etaPairIndexNormalizedTailConstant_ne_zero_zdss004 s)
  have hnormalizedNe : ∀ᶠ k : ℕ in atTop,
      etaPairIndexNormalizedRotatedPartial s k ≠ 0 :=
    hpartial.eventually (eventually_ne_nhds hlimitNe)
  filter_upwards [hnormalizedNe] with k hk
  apply etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio
  intro hpartialZero
  apply hk
  simp [etaPairIndexNormalizedRotatedPartial, hpartialZero]

/-! ## Exact U1/U2 compatibility obstruction -/

/--
An off-critical zero would simultaneously carry both nonzero normalized
endpoint rates, the finite positive self-normalized ratio limit, the exact
source/mode ratio factorization, and normalized-Gap divergence.  Thus the
available two-sided U1 tail rates do not imply U2 anti-divergence.
-/
structure EtaDualEndpointRateNormalizedGapCompatibilityCertificate
    (s : ℂ) : Prop where
  endpoint_rates : EtaDualEndpointNormalizedRateCertificate s
  normalized_ratio_tendsto :
    Tendsto (fun k : ℕ => etaDualEndpointNormalizedNormRatio k s)
      atTop (nhds (etaDualEndpointNormalizedNormRatioLimit s))
  normalized_ratio_limit_pos :
    0 < etaDualEndpointNormalizedNormRatioLimit s
  source_mode_ratio_bridge :
    ∀ᶠ k : ℕ in atTop,
      etaDualEndpointRawNormRatio k s =
        etaEndpointIncrementMirrorRatio s k *
          etaDualEndpointNormalizedNormRatio k s
  normalized_gap_tendsto_atTop :
    Tendsto (fun k : ℕ => etaEndpointIncrementMirrorGap s k)
      atTop atTop

/-- Build the compatibility certificate under the hypothetical off-critical-zero case. -/
theorem etaDualEndpointRateNormalizedGapCompatibilityCertificate_of_offCriticalZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    EtaDualEndpointRateNormalizedGapCompatibilityCertificate s := by
  exact
    { endpoint_rates :=
        etaDualEndpointNormalizedRateCertificate_of_nontrivialRiemannZetaZero
          hs him
      normalized_ratio_tendsto :=
        etaDualEndpointNormalizedNormRatio_tendsto_limit_of_nontrivialRiemannZetaZero
          hs him
      normalized_ratio_limit_pos :=
        etaDualEndpointNormalizedNormRatioLimit_pos s
      source_mode_ratio_bridge :=
        eventually_etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio_of_nontrivialRiemannZetaZero
          hs him
      normalized_gap_tendsto_atTop :=
        etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half hre }

#print axioms etaPairIndexNormalizedRotatedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
#print axioms etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero
#print axioms etaPairIndexNormalizedPartialNorm_tendsto_constantNorm_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointNormalizedRateCertificate_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointNormalizedNormRatio_tendsto_limit_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio
#print axioms eventually_etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointRateNormalizedGapCompatibilityCertificate_of_offCriticalZero

end DkMath.RH.CFBRCProjection
