/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeCompatibilityAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseBridge"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
Scalar transverse discrepancy between the dominant eta endpoint and the
canonical completed-zeta slope carrier, measured in the same fixed slope frame.

Unlike full carrier difference, this retains only the one real coordinate
actually consumed by the moving-line collision route.
-/
noncomputable def etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError
    (k : ℕ) (s : ℂ) : ℝ :=
  complexRealLineDefect
      (completedZetaCanonicalSlopeDirection s)
      (etaCriticalMirrorDominantNormalizedEndpointCarrier k s) -
    complexRealLineDefect
      (completedZetaCanonicalSlopeDirection s)
      (completedZetaCanonicalSlopeCarrier k s)

/-- The scalar bridge is exactly the slope-frame defect of the carrier difference. -/
theorem etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_differenceDefect
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s =
      complexRealLineDefect
        (completedZetaCanonicalSlopeDirection s)
        (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
          completedZetaCanonicalSlopeCarrier k s) := by
  simp [etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError,
    complexRealLineDefect, mul_sub]

/-- At a nontrivial zero, the slope carrier is the normalized nearby completed-zeta value. -/
theorem completedZetaCanonicalSlopeCarrier_eq_normalizedNearbyValue_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    completedZetaCanonicalSlopeCarrier k s =
      (completedZetaCanonicalDisplacement k)⁻¹ *
        completedRiemannZeta
          (s + completedZetaCanonicalDisplacement k) := by
  unfold completedZetaCanonicalSlopeCarrier
  rw [completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero hs, sub_zero]

/--
On the zero locus, the scalar bridge is the completed-zeta slope-frame defect
of one explicit finite difference: dominant eta endpoint minus normalized
nearby completed-zeta value.
-/
theorem etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_nearbyValueDefect_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s =
      complexRealLineDefect
        (completedZetaCanonicalSlopeDirection s)
        (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
          (completedZetaCanonicalDisplacement k)⁻¹ *
            completedRiemannZeta
              (s + completedZetaCanonicalDisplacement k)) := by
  rw [
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_differenceDefect,
    completedZetaCanonicalSlopeCarrier_eq_normalizedNearbyValue_of_zero hs]

/--
The remaining scalar analytic bridge: endpoint and canonical completed-zeta
slope carrier have asymptotically the same transverse coordinate on the
standard nontrivial zero locus.
-/
def EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s)
      atTop (nhds 0)

/--
Because the canonical slope carrier already approaches its completed-zeta
slope line, scalar bridge collapse is exactly the endpoint line-compatibility
condition.
-/
theorem etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_iff_lineCompatibility :
    EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility := by
  constructor
  · intro hbridge s hs him
    have herror := hbridge hs him
    have hslope := completedZetaCanonicalSlopeCarrier_tendsto_global_line hs
    have hsum := herror.add hslope
    have hsum' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s +
              complexRealLineDefect
                (completedZetaCanonicalSlopeDirection s)
                (completedZetaCanonicalSlopeCarrier k s))
          atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    refine hsum'.congr' (Eventually.of_forall fun k => ?_)
    unfold etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError
    ring
  · intro hline s hs him
    have hendpoint := hline hs him
    have hslope := completedZetaCanonicalSlopeCarrier_tendsto_global_line hs
    have hdiff := hendpoint.sub hslope
    simpa [etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError] using hdiff

/-- Full endpoint/slope value compatibility implies the weaker scalar bridge. -/
theorem etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_of_valueCompatibility
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse :=
  etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_iff_lineCompatibility.mpr
    (etaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility_of_valueCompatibility
      hcompat)

/-- RH follows from the one-dimensional endpoint/slope transverse bridge. -/
theorem riemannHypothesis_of_endpointCompletedZetaSlopeTransverseBridgeCollapse
    (hbridge :
      EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSlopeLineCompatibility
    (etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_iff_lineCompatibility.mp
      hbridge)

#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_differenceDefect
#print axioms completedZetaCanonicalSlopeCarrier_eq_normalizedNearbyValue_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_nearbyValueDefect_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse_iff_lineCompatibility
#print axioms riemannHypothesis_of_endpointCompletedZetaSlopeTransverseBridgeCollapse

end DkMath.RH.CFBRCProjection
