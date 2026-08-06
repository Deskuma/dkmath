/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfRHEquivalenceAudit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- On the critical line, the Euler half-endpoint main carrier is exactly zero. -/
theorem etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_zero_of_re_eq_half
    {s : ℂ} (hcritical : s.re = (1 : ℝ) / 2) (k : ℕ) :
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s = 0 := by
  have hmirror : criticalMirror s = s :=
    (criticalMirror_eq_self_iff_re_eq_half s).2 hcritical
  unfold etaCriticalMirrorDominantWeightedTailEulerMainCarrier
  rw [hmirror]
  ring

/-- The critical-safe single dominant carrier is exactly zero on the critical line. -/
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrier_eq_zero_of_re_eq_half
    {s : ℂ} (hcritical : s.re = (1 : ℝ) / 2) (k : ℕ) :
    etaCriticalMirrorDominantEulerHalfEndpointCarrier k s = 0 := by
  simp [etaCriticalMirrorDominantEulerHalfEndpointCarrier, hcritical,
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_zero_of_re_eq_half]

/-- Its completed-zeta slope-frame transverse error is therefore exactly zero. -/
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError_eq_zero_of_re_eq_half
    {s : ℂ} (hcritical : s.re = (1 : ℝ) / 2) (k : ℕ) :
    etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError k s = 0 := by
  simp [etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError,
    etaCriticalMirrorDominantEulerHalfEndpointCarrier_eq_zero_of_re_eq_half
      hcritical]

/-- RH supplies the critical-safe dominant-half transverse-collapse contract. -/
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse := by
  intro s hs _him
  have hcritical : s.re = (1 : ℝ) / 2 :=
    (riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH) s hs
  simpa [etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError_eq_zero_of_re_eq_half
    hcritical] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/--
Audit boundary: the final critical-safe dominant-half contract is exactly
logically equivalent to the Riemann Hypothesis.

This theorem does not prove RH.  It records that further replacement of the
remaining research beacon by this contract alone is only a reformulation of
the target theorem.
-/
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_dominantEulerHalfEndpointCarrierTransverseCollapse
  · exact
      etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_of_riemannHypothesis

#print axioms etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_zero_of_re_eq_half
#print axioms etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_of_riemannHypothesis
#print axioms etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis

end DkMath.RH.CFBRCProjection
