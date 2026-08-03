/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorEnergyCollapse
import DkMath.RH.CFBRC.EtaMirrorAmplitudeDecoder
import DkMath.RH.CFBRC.OffCriticalExclusionGeneral
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaEndpointIncrementDecoder"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-- One-step increment of the finite eta endpoint. -/
noncomputable def etaEndpointIncrement (N : ℕ) (s : ℂ) : ℂ :=
  etaPartialEndpoint (N + 1) s - etaPartialEndpoint N s

/-- The endpoint increment is exactly the newly appended signed eta vector. -/
@[simp] theorem etaEndpointIncrement_eq_etaSignedVector
    (N : ℕ) (s : ℂ) :
    etaEndpointIncrement N s = etaSignedVector s N := by
  simp [etaEndpointIncrement, etaPartialEndpoint, finiteEndpoint,
    Finset.sum_range_succ]

/-- Mirror/original ratio of endpoint-increment magnitudes. -/
noncomputable def etaEndpointIncrementMirrorRatio (s : ℂ) (N : ℕ) : ℝ :=
  ‖etaEndpointIncrement N (criticalMirror s)‖ /
    ‖etaEndpointIncrement N s‖

/-- Endpoint increments reproduce the genuine eta-term amplitude ratio exactly. -/
theorem etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio
    (s : ℂ) (N : ℕ) :
    etaEndpointIncrementMirrorRatio s N = etaMirrorAmplitudeRatio s N := by
  simp [etaEndpointIncrementMirrorRatio, etaMirrorAmplitudeRatio]

/--
Base-two centered-coordinate decoder written only through adjacent finite eta
endpoints at the original and critical-mirror points.
-/
noncomputable def etaEndpointIncrementDecoder (s : ℂ) : ℝ :=
  Real.log (etaEndpointIncrementMirrorRatio s 1) / (2 * Real.log 2)

/-- The endpoint-increment decoder is exactly the term-amplitude decoder. -/
theorem etaEndpointIncrementDecoder_eq_etaMirrorAmplitudeDecoder
    (s : ℂ) :
    etaEndpointIncrementDecoder s = etaMirrorAmplitudeDecoder s := by
  rw [etaEndpointIncrementDecoder, etaMirrorAmplitudeDecoder,
    etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio]

/-- Endpoint increments recover the centered real coordinate exactly. -/
theorem etaEndpointIncrementDecoder_eq_centeredSigma
    (s : ℂ) :
    etaEndpointIncrementDecoder s = centeredSigma s.re := by
  rw [etaEndpointIncrementDecoder_eq_etaMirrorAmplitudeDecoder,
    etaMirrorAmplitudeDecoder_eq_centeredSigma]

/-- Unit endpoint-increment ratio is exactly the critical-line condition. -/
theorem etaEndpointIncrementMirrorRatio_one_eq_one_iff_re_eq_half
    (s : ℂ) :
    etaEndpointIncrementMirrorRatio s 1 = 1 ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hratio
    have hdecoder : etaEndpointIncrementDecoder s = 0 := by
      rw [etaEndpointIncrementDecoder, hratio]
      norm_num
    have hcenter : centeredSigma s.re = 0 := by
      rwa [etaEndpointIncrementDecoder_eq_centeredSigma] at hdecoder
    exact (centeredSigma_eq_zero_iff s.re).mp hcenter
  · intro hre
    have hcenter : centeredSigma s.re = 0 :=
      (centeredSigma_eq_zero_iff s.re).2 hre
    rw [etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio,
      etaMirrorAmplitudeRatio_one_eq_two_rpow, hcenter]
    norm_num

/--
For every positive CFBRC degree, endpoint-increment balance selects exactly the
same zero locus as the standard off-critical CFBRC projection.
-/
theorem offCriticalCFBRC_eq_zero_iff_endpointIncrementMirrorRatio_eq_one
    {d : ℕ} (hd : 0 < d) (s : ℂ) (Θ : ℝ) :
    offCriticalCFBRC d s.re Θ = 0 ↔
      etaEndpointIncrementMirrorRatio s 1 = 1 := by
  rw [offCriticalCFBRC_eq_zero_iff_re_eq_half hd,
    etaEndpointIncrementMirrorRatio_one_eq_one_iff_re_eq_half]

/--
The remaining zero-preserving obligation in endpoint language.  This does not
assume the critical-line conclusion; it names the exact increment-balance fact
needed to build the standard CFBRC bridge.
-/
def EtaEndpointIncrementBalancedOnNontrivialZeros : Prop :=
  ∀ {s : ℂ}, NontrivialRiemannZetaZero s →
    etaEndpointIncrementMirrorRatio s 1 = 1

/--
The global endpoint-increment balance condition is exactly the Riemann
hypothesis.  Hence it must not be imported as an auxiliary lemma when building
a non-circular proof of the zero-preserving map.
-/
theorem etaEndpointIncrementBalancedOnNontrivialZeros_iff_riemannHypothesis :
    EtaEndpointIncrementBalancedOnNontrivialZeros ↔ RiemannHypothesis := by
  constructor
  · intro hbalance
    rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
    intro s hs
    exact
      (etaEndpointIncrementMirrorRatio_one_eq_one_iff_re_eq_half s).mp
        (hbalance hs)
  · intro hRH s hs
    exact
      (etaEndpointIncrementMirrorRatio_one_eq_one_iff_re_eq_half s).2
        ((riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH) s hs)

/-- Endpoint-increment balance supplies the positive-degree standard CFBRC map. -/
def zeroToCFBRCBridge_of_endpointIncrementBalance
    (hbalance : EtaEndpointIncrementBalancedOnNontrivialZeros)
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ) :
    ZeroToCFBRCBridge NontrivialRiemannZetaZero where
  d := d
  hd := hd
  phase := phase
  map_zero := by
    intro s hs
    exact
      (offCriticalCFBRC_eq_zero_iff_endpointIncrementMirrorRatio_eq_one
        hd s (phase s)).2
        (hbalance hs)

end DkMath.RH.CFBRCProjection
