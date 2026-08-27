/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseBridge
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaTailReduction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyTransverseBridge"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The side-aware dominant complete eta-tail carrier.

It uses the same dominant index power as the finite endpoint and the complete
remaining paired defect tail beginning at the same pair index.
-/
noncomputable def etaCriticalMirrorDominantWeightedTailCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantIndexPower k s *
    (-etaCriticalMirrorDefectPairTail (k + 1) s)

/--
At a nonreal nontrivial zero, the dominant endpoint is exactly the dominant
weighted complete-tail carrier at every retained index.
-/
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_weightedTailCarrier_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorDominantNormalizedEndpointCarrier k s =
      etaCriticalMirrorDominantWeightedTailCarrier k s := by
  rw [etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_finiteEtaCarrier]
  unfold etaCriticalMirrorDominantFiniteEtaCarrier
  rw [etaCriticalMirrorFinitePairedEtaDefect_eq_neg_tail_of_zero hs him]
  rfl

/--
Finite-index transverse comparison between the dominant weighted eta tail and
the normalized nearby completed-zeta value.
-/
noncomputable def etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError
    (k : ℕ) (s : ℂ) : ℝ :=
  complexRealLineDefect
    (completedZetaCanonicalSlopeDirection s)
    (etaCriticalMirrorDominantWeightedTailCarrier k s -
      (completedZetaCanonicalDisplacement k)⁻¹ *
        completedRiemannZeta
          (s + completedZetaCanonicalDisplacement k))

/--
On the zero locus, the endpoint/slope scalar bridge is exactly the explicit
weighted-tail / nearby-completed-zeta transverse bridge.
-/
theorem etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_tailNearbyError_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError k s =
      etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError k s := by
  rw [
    etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_nearbyValueDefect_of_zero
      hs,
    etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_weightedTailCarrier_of_zero
      hs him]
  rfl

/--
The remaining analytic bridge expressed entirely through an explicit complete
eta tail and one nearby completed-zeta value.
-/
def EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError
          k s)
      atTop (nhds 0)

/--
The endpoint/slope scalar bridge and the weighted-tail / nearby-value bridge are
exactly equivalent on the nontrivial zero locus.
-/
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_endpointSlopeBridgeCollapse :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeCollapse := by
  constructor
  · intro htail s hs him
    have h := htail hs him
    refine h.congr' (Eventually.of_forall fun k => ?_)
    exact
      (etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_tailNearbyError_of_zero
        hs him k).symm
  · intro hbridge s hs him
    have h := hbridge hs him
    refine h.congr' (Eventually.of_forall fun k => ?_)
    exact
      etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_tailNearbyError_of_zero
        hs him k

/-- RH follows from the explicit weighted-tail / nearby-completed-zeta bridge. -/
theorem riemannHypothesis_of_weightedTailCompletedZetaNearbyTransverseBridgeCollapse
    (htail :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSlopeTransverseBridgeCollapse
    (etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_endpointSlopeBridgeCollapse.mp
      htail)

#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_weightedTailCarrier_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaSlopeTransverseBridgeError_eq_tailNearbyError_of_zero
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_endpointSlopeBridgeCollapse
#print axioms riemannHypothesis_of_weightedTailCompletedZetaNearbyTransverseBridgeCollapse

end DkMath.RH.CFBRCProjection
