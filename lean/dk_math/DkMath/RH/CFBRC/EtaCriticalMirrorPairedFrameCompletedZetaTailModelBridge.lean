/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailPhaseLock
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailModelBridge"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology

/--
The dominant endpoint is asymptotically represented by one explicit
completed-zeta / Hardy-frame model on the nontrivial zero locus.

Through the already proved finite-eta and complete-tail reductions, this is the
same as approximating the dominant-weighted complete tail.
-/
def EtaCriticalMirrorDominantEndpointModelApproximation
    (model : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantNormalizedEndpointCarrier k s - model k s)
      atTop (nhds 0)

/--
The intermediate model lies asymptotically on the fixed projective line
selected by the completed-zeta canonical slope direction.
-/
def EtaCriticalMirrorCompletedZetaModelOrbitResidualCollapse
    (model : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        model k s -
          completedZetaCanonicalSlopeProjectivePhase s * conj (model k s))
      atTop (nhds 0)

/--
A model approximation and a model orbit collapse imply the exact weighted-tail
orbit collapse consumed by the Ultra phase-lock collision.
-/
theorem etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse_of_model
    {model : ℕ → ℂ → ℂ}
    (happrox : EtaCriticalMirrorDominantEndpointModelApproximation model)
    (horbit : EtaCriticalMirrorCompletedZetaModelOrbitResidualCollapse model) :
    EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse := by
  intro s hs him
  have herror := happrox hs him
  have hconjError :
      Tendsto
        (fun k : ℕ =>
          conj
            (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              model k s))
        atTop (nhds 0) := by
    have h := (Complex.continuous_conj.tendsto 0).comp herror
    simpa [Function.comp_def] using h
  have hphaseConjError :
      Tendsto
        (fun k : ℕ =>
          completedZetaCanonicalSlopeProjectivePhase s *
            conj
              (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
                model k s))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto
          (fun _ : ℕ => completedZetaCanonicalSlopeProjectivePhase s)
          atTop (nhds (completedZetaCanonicalSlopeProjectivePhase s)) from
        tendsto_const_nhds).mul hconjError
  have hmodelPlusError :
      Tendsto
        (fun k : ℕ =>
          (model k s -
              completedZetaCanonicalSlopeProjectivePhase s *
                conj (model k s)) +
            (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              model k s))
        atTop (nhds 0) := by
    simpa using (horbit hs him).add herror
  have htotal :
      Tendsto
        (fun k : ℕ =>
          (model k s -
              completedZetaCanonicalSlopeProjectivePhase s *
                conj (model k s)) +
            (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              model k s) -
            completedZetaCanonicalSlopeProjectivePhase s *
              conj
                (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
                  model k s))
        atTop (nhds 0) := by
    have h := hmodelPlusError.add hphaseConjError.neg
    simpa only [sub_eq_add_neg, add_zero, neg_zero] using h
  have hendpointResidual :
      Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            completedZetaCanonicalSlopeProjectivePhase s *
              conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s))
        atTop (nhds 0) := by
    refine htotal.congr' (Eventually.of_forall fun k => ?_)
    rw [map_sub]
    ring
  refine hendpointResidual.congr' (Eventually.of_forall fun k => ?_)
  exact
    (etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual_eq_endpointPhaseResidual_of_zero
      hs him k).symm

/-- RH follows once one explicit model discharges the two independent bridges. -/
theorem riemannHypothesis_of_completedZetaTailModel
    {model : ℕ → ℂ → ℂ}
    (happrox : EtaCriticalMirrorDominantEndpointModelApproximation model)
    (horbit : EtaCriticalMirrorCompletedZetaModelOrbitResidualCollapse model) :
    RiemannHypothesis :=
  riemannHypothesis_of_completedZetaWeightedTailPhaseLockCollision
    (etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse_of_model
      happrox horbit)

#print axioms etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse_of_model
#print axioms riemannHypothesis_of_completedZetaTailModel

end DkMath.RH.CFBRCProjection
