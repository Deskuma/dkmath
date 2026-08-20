/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorEnergyCollapse
import DkMath.RH.CFBRC.PrimeMirrorEtaAsymptoticDichotomy
import DkMath.RH.CFBRC.ZeroDerivedPrimeCoordinateSourceRankAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.ZeroDerivedDualEndpointPositiveScalarCoercivityAudit"

/-!
# ZDSS-003: dual-endpoint positive-scalar coercivity audit

This module tests positive scalars built directly from the two ordinary
paired-Eta endpoint sources isolated by ZDSS-001.  Their squared-norm sum is a
genuine zero-derived upper-side quantity: at a nonreal standard zeta zero it
has separate tail bounds and tends to zero.

The same scalar does not supply horizontal coercivity.  Norm imbalance and
the symmetric/antisymmetric polarizations are bounded by the total endpoint
energy, while any fixed positive lower coefficient for `centeredSigma ^ 2`
would already force the critical-line conclusion.  The final theorem records
that exact frontier without postulating such a coefficient or importing the
historical endpoint-Gap-to-UnitGap provider.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-! ## Source-matched dual-endpoint energy -/

/--
Squared-norm energy of the two separate paired-Eta endpoint sources at `s`
and its critical mirror.
-/
noncomputable def etaDualEndpointTotalEnergy (K : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (etaPairedPartial K s) +
    Complex.normSq (etaPairedPartial K (criticalMirror s))

/--
Explicit sum of the two ordinary paired-tail power bounds.  This is an
upper-side majorant, not a centered-coordinate lower bound.
-/
noncomputable def etaDualEndpointPowerUpperBound (K : ℕ) (s : ℂ) : ℝ :=
  (‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re)) ^ 2 +
    (‖criticalMirror s‖ *
      (((K : ℝ) ^ (-(criticalMirror s).re)) /
        (criticalMirror s).re)) ^ 2

/-- The new source-matched energy is exactly the old endpoint energy at `2K`. -/
theorem etaDualEndpointTotalEnergy_eq_evenEndpointTotalEnergy
    (K : ℕ) (s : ℂ) :
    etaDualEndpointTotalEnergy K s =
      etaMirrorEndpointTotalEnergy (2 * K) s := by
  simp [etaDualEndpointTotalEnergy, etaMirrorEndpointTotalEnergy,
    etaPartialEndpoint_two_mul_eq_etaPairedPartial]

/-- The dual-endpoint energy is nonnegative at every cutoff. -/
theorem etaDualEndpointTotalEnergy_nonneg (K : ℕ) (s : ℂ) :
    0 ≤ etaDualEndpointTotalEnergy K s := by
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/--
At a nonreal standard zeta zero, the two independent tail estimates bound the
dual-endpoint energy by their squared power majorants.
-/
theorem etaDualEndpointTotalEnergy_le_powerUpperBound_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    {K : ℕ} (hK : 1 ≤ K) :
    etaDualEndpointTotalEnergy K s ≤
      etaDualEndpointPowerUpperBound K s := by
  have horiginal :=
    norm_etaPairedPartial_le_powerBound_of_nontrivialRiemannZetaZero
      hs him hK
  have hmirror :=
    norm_etaPairedPartial_criticalMirror_le_powerBound_of_nontrivialRiemannZetaZero
      hs him hK
  have horiginalBoundNonneg :
      0 ≤ ‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re) := by
    have ho := nontrivialRiemannZetaZero_re_pos hs
    positivity
  have hmirrorBoundNonneg :
      0 ≤ ‖criticalMirror s‖ *
        (((K : ℝ) ^ (-(criticalMirror s).re)) /
          (criticalMirror s).re) := by
    have hm := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
    positivity
  unfold etaDualEndpointTotalEnergy etaDualEndpointPowerUpperBound
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (etaPairedPartial K s),
    norm_nonneg (etaPairedPartial K (criticalMirror s))]

/-- The explicit dual-tail power upper bound tends to zero in the open strip. -/
theorem etaDualEndpointPowerUpperBound_tendsto_zero
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re) :
    Tendsto (fun K : ℕ => etaDualEndpointPowerUpperBound K s)
      atTop (nhds 0) := by
  have hnat : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have horiginalPow := (tendsto_rpow_neg_atTop hs).comp hnat
  have hmirrorPow := (tendsto_rpow_neg_atTop hm).comp hnat
  have horiginal : Tendsto
      (fun K : ℕ => ‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul horiginalPow).mul
        (show Tendsto (fun _ : ℕ => (s.re)⁻¹)
            atTop (nhds (s.re)⁻¹) from tendsto_const_nhds)
  have hmirror : Tendsto
      (fun K : ℕ => ‖criticalMirror s‖ *
        (((K : ℝ) ^ (-(criticalMirror s).re)) /
          (criticalMirror s).re))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul hmirrorPow).mul
        (show Tendsto (fun _ : ℕ => ((criticalMirror s).re)⁻¹)
            atTop (nhds ((criticalMirror s).re)⁻¹) from
          tendsto_const_nhds)
  simpa [etaDualEndpointPowerUpperBound] using
    (horiginal.pow 2).add (hmirror.pow 2)

/--
The source-matched dual-endpoint energy tends to zero at every nonreal
standard zeta zero.  This is the complete upper-side conclusion of candidate
A; it has no critical-line consequence by itself.
-/
theorem etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun K : ℕ => etaDualEndpointTotalEnergy K s)
      atTop (nhds 0) := by
  have henergy :=
    (etaCriticalMirror_pairEnergy_tendsto_zero hs him).1.comp
      tendsto_two_mul_atTop
  simpa only [etaDualEndpointTotalEnergy_eq_evenEndpointTotalEnergy,
    Function.comp_def] using
    henergy

/-! ## Degenerate scalar combinations of the same sources -/

/-- Squared imbalance of the norms of the two source endpoints. -/
noncomputable def etaDualEndpointNormImbalanceSq (K : ℕ) (s : ℂ) : ℝ :=
  (‖etaPairedPartial K s‖ -
    ‖etaPairedPartial K (criticalMirror s)‖) ^ 2

/-- Norm imbalance is nonnegative but is bounded above by total source energy. -/
theorem etaDualEndpointNormImbalanceSq_le_totalEnergy
    (K : ℕ) (s : ℂ) :
    etaDualEndpointNormImbalanceSq K s ≤
      etaDualEndpointTotalEnergy K s := by
  unfold etaDualEndpointNormImbalanceSq etaDualEndpointTotalEnergy
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [mul_nonneg (norm_nonneg (etaPairedPartial K s))
    (norm_nonneg (etaPairedPartial K (criticalMirror s)))]

/-- At a nonreal zero, norm imbalance collapses together with total energy. -/
theorem etaDualEndpointNormImbalanceSq_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun K : ℕ => etaDualEndpointNormImbalanceSq K s)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him)
  · exact Eventually.of_forall fun K => sq_nonneg _
  · exact Eventually.of_forall fun K =>
      etaDualEndpointNormImbalanceSq_le_totalEnergy K s

/-- The squared symmetric endpoint sum is at most twice the total energy. -/
theorem normSq_etaDualEndpoint_add_le_two_mul_totalEnergy
    (K : ℕ) (s : ℂ) :
    Complex.normSq
        (etaPairedPartial K s + etaPairedPartial K (criticalMirror s)) ≤
      2 * etaDualEndpointTotalEnergy K s := by
  have hparallelogram :=
    etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy (2 * K) s
  have hgapNonneg : 0 ≤ etaMirrorEndpointGap (2 * K) s :=
    Complex.normSq_nonneg _
  simp only [etaMirrorEndpointBig, etaMirrorEndpointGap,
    etaMirrorEndpointTotalEnergy,
    etaPartialEndpoint_two_mul_eq_etaPairedPartial] at hparallelogram hgapNonneg
  simpa [etaDualEndpointTotalEnergy] using
    (show Complex.normSq
          (etaPairedPartial K s + etaPairedPartial K (criticalMirror s)) ≤
        2 * (Complex.normSq (etaPairedPartial K s) +
          Complex.normSq (etaPairedPartial K (criticalMirror s))) by
      linarith)

/-- The squared antisymmetric endpoint difference is also at most twice the energy. -/
theorem normSq_etaDualEndpoint_sub_le_two_mul_totalEnergy
    (K : ℕ) (s : ℂ) :
    Complex.normSq
        (etaPairedPartial K s - etaPairedPartial K (criticalMirror s)) ≤
      2 * etaDualEndpointTotalEnergy K s := by
  have hparallelogram :=
    etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy (2 * K) s
  have hbigNonneg : 0 ≤ etaMirrorEndpointBig (2 * K) s :=
    Complex.normSq_nonneg _
  simp only [etaMirrorEndpointBig, etaMirrorEndpointGap,
    etaMirrorEndpointTotalEnergy,
    etaPartialEndpoint_two_mul_eq_etaPairedPartial] at hparallelogram hbigNonneg
  simpa [etaDualEndpointTotalEnergy] using
    (show Complex.normSq
          (etaPairedPartial K s - etaPairedPartial K (criticalMirror s)) ≤
        2 * (Complex.normSq (etaPairedPartial K s) +
          Complex.normSq (etaPairedPartial K (criticalMirror s))) by
      linarith)

/-- At a nonreal zero, the symmetric polarization energy tends to zero. -/
theorem normSq_etaDualEndpoint_add_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => Complex.normSq
        (etaPairedPartial K s + etaPairedPartial K (criticalMirror s)))
      atTop (nhds 0) := by
  have henergy :=
    etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  have hupper : Tendsto
      (fun K : ℕ => 2 * etaDualEndpointTotalEnergy K s)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul henergy
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun K => Complex.normSq_nonneg _
  · exact Eventually.of_forall fun K =>
      normSq_etaDualEndpoint_add_le_two_mul_totalEnergy K s

/-- At a nonreal zero, the antisymmetric polarization energy tends to zero. -/
theorem normSq_etaDualEndpoint_sub_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => Complex.normSq
        (etaPairedPartial K s - etaPairedPartial K (criticalMirror s)))
      atTop (nhds 0) := by
  have henergy :=
    etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  have hupper : Tendsto
      (fun K : ℕ => 2 * etaDualEndpointTotalEnergy K s)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul henergy
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun K => Complex.normSq_nonneg _
  · exact Eventually.of_forall fun K =>
      normSq_etaDualEndpoint_sub_le_two_mul_totalEnergy K s

/-! ## Mode-rate boundary -/

/--
If a standard zero were off the critical line, its raw term-amplitude Gap
would still tend to zero, while the source-revealing `(K + 1)` normalization
would diverge.  This coexistence identifies the cutoff-rate information lost
by all unnormalized endpoint-energy candidates above.
-/
theorem etaMirrorAmplitudeGap_zero_normalized_atTop_of_nontrivialRiemannZetaZero_offCritical
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto (fun K : ℕ => etaMirrorAmplitudeGap s K) atTop (nhds 0) ∧
      Tendsto (fun K : ℕ =>
        ((K + 1 : ℕ) : ℝ) * etaMirrorAmplitudeGap s K)
        atTop atTop := by
  exact etaMirrorAmplitudeGap_raw_zero_normalized_atTop
    (nontrivialRiemannZetaZero_re_pos hs)
    (nontrivialRiemannZetaZero_re_lt_one hs) hre

/-! ## Exact centered-coercivity frontier -/

/--
Any eventually valid lower bound with a fixed positive coefficient and the
zero-derived dual-endpoint energy already forces the critical line.  The
theorem is an obstruction/classification result: this module supplies no term
of the required lower-bound hypothesis.
-/
theorem re_eq_half_of_eventually_dualEndpoint_uniform_centered_coercivity
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ᶠ K : ℕ in atTop,
      c * centeredSigma s.re ^ 2 ≤ etaDualEndpointTotalEnergy K s) :
    s.re = (1 : ℝ) / 2 := by
  have hlimit :=
    etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  have hle : c * centeredSigma s.re ^ 2 ≤ 0 := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit hcoercive
  have hcenter : centeredSigma s.re = 0 := by
    by_contra hne
    have hpos : 0 < c * centeredSigma s.re ^ 2 :=
      mul_pos hc (sq_pos_of_ne_zero hne)
    linarith
  exact (centeredSigma_eq_zero_iff s.re).mp hcenter

/-!
The rate comparison is deliberately left in its existing exact form:
`etaMirrorAmplitudeGap_raw_zero_normalized_atTop` shows that raw mode Gap can
vanish off the critical line while multiplication by `K + 1` makes the
normalized Gap diverge.  Thus removing this cutoff factor is precisely where
the endpoint upper-side loses the horizontal information required by a
centered lower bound.
-/

#print axioms etaDualEndpointTotalEnergy_le_powerUpperBound_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointPowerUpperBound_tendsto_zero
#print axioms etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointNormImbalanceSq_le_totalEnergy
#print axioms etaDualEndpointNormImbalanceSq_tendsto_zero_of_nontrivialRiemannZetaZero
#print axioms normSq_etaDualEndpoint_add_tendsto_zero_of_nontrivialRiemannZetaZero
#print axioms normSq_etaDualEndpoint_sub_tendsto_zero_of_nontrivialRiemannZetaZero
#print axioms etaMirrorAmplitudeGap_zero_normalized_atTop_of_nontrivialRiemannZetaZero_offCritical
#print axioms re_eq_half_of_eventually_dualEndpoint_uniform_centered_coercivity

end DkMath.RH.CFBRCProjection
