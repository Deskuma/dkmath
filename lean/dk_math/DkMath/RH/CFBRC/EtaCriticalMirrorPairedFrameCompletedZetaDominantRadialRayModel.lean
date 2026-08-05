/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailModelBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantRadialRayModel"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
A completed-zeta slope ray with an arbitrary real amplitude.

The direction is supplied entirely by completed zeta.  The amplitude may depend
on the truncation index and the observation point, but remains real, so every
value lies exactly on the fixed projective line selected by the canonical
completed-zeta slope direction.
-/
noncomputable def completedZetaCanonicalSlopeRayModel
    (amplitude : ℕ → ℂ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  completedZetaCanonicalSlopeDirection s *
    ((amplitude k s : ℝ) : ℂ)

/-- Every real-amplitude slope-ray value has zero completed-zeta line defect. -/
theorem completedZetaCanonicalSlopeRayModel_realLineDefect_eq_zero
    (amplitude : ℕ → ℂ → ℝ) (k : ℕ) (s : ℂ) :
    complexRealLineDefect
        (completedZetaCanonicalSlopeDirection s)
        (completedZetaCanonicalSlopeRayModel amplitude k s) = 0 := by
  unfold complexRealLineDefect
  unfold completedZetaCanonicalSlopeRayModel
  rw [← mul_assoc]
  rw [inv_mul_cancel₀ (completedZetaCanonicalSlopeDirection_ne_zero s)]
  simp

/--
Every real-amplitude slope ray satisfies the completed-zeta projective orbit
condition unconditionally.  Thus the orbit bridge is architectural rather than
an additional analytic research premise.
-/
theorem completedZetaCanonicalSlopeRayModel_orbitResidualCollapse
    (amplitude : ℕ → ℂ → ℝ) :
    EtaCriticalMirrorCompletedZetaModelOrbitResidualCollapse
      (completedZetaCanonicalSlopeRayModel amplitude) := by
  intro s _hs _him
  have hline :
      Tendsto
        (fun k : ℕ =>
          complexRealLineDefect
            (completedZetaCanonicalSlopeDirection s)
            (completedZetaCanonicalSlopeRayModel amplitude k s))
        atTop (nhds 0) := by
    simpa [completedZetaCanonicalSlopeRayModel_realLineDefect_eq_zero]
      using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hresidual :=
    tendsto_phaseResidual_zero_of_complexRealLineDefect_tendsto_zero
      (completedZetaCanonicalSlopeDirection_ne_zero s) hline
  simpa [completedZetaCanonicalSlopeProjectivePhase] using hresidual

/--
The explicit side-aware radial coefficient of the dominant normalized eta
half-tail main term.

The left side carries the negative half-tail sign; the right side carries the
positive mirror half-tail sign.  The formula depends only on the retained
truncation index and the explicit Euler half-main radial ratio.
-/
noncomputable def etaCriticalMirrorDominantRadialAmplitude
    (k : ℕ) (s : ℂ) : ℝ :=
  if s.re ≤ (1 : ℝ) / 2 then
    -(((1 : ℝ) / 2) *
      (etaPairIndexToSuccessorEndpointRatio k ^ s.re))
  else
    ((1 : ℝ) / 2) *
      (etaPairIndexToSuccessorEndpointRatio k ^ (criticalMirror s).re)

/--
Canonical completed-zeta / eta-tail hybrid model.

Its radial magnitude is the explicit same-index dominant Euler half-tail
coefficient, while its direction is the fixed canonical completed-zeta slope
ray.  It does not inspect or copy the endpoint carrier.
-/
noncomputable def etaCriticalMirrorCompletedZetaDominantRadialRayModel
    (k : ℕ) (s : ℂ) : ℂ :=
  completedZetaCanonicalSlopeRayModel
    etaCriticalMirrorDominantRadialAmplitude k s

/-- The canonical dominant radial ray model has exact fixed-phase orbit collapse. -/
theorem etaCriticalMirrorCompletedZetaDominantRadialRayModel_orbitResidualCollapse :
    EtaCriticalMirrorCompletedZetaModelOrbitResidualCollapse
      etaCriticalMirrorCompletedZetaDominantRadialRayModel := by
  exact
    completedZetaCanonicalSlopeRayModel_orbitResidualCollapse
      etaCriticalMirrorDominantRadialAmplitude

/--
Only one analytic bridge now remains: approximation of the dominant endpoint by
the explicit completed-zeta dominant radial ray model.
-/
def EtaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation : Prop :=
  EtaCriticalMirrorDominantEndpointModelApproximation
    etaCriticalMirrorCompletedZetaDominantRadialRayModel

/-- RH follows from approximation by the explicit dominant radial ray model. -/
theorem riemannHypothesis_of_completedZetaDominantRadialRayModelApproximation
    (happrox :
      EtaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation) :
    RiemannHypothesis :=
  riemannHypothesis_of_completedZetaTailModel
    happrox
    etaCriticalMirrorCompletedZetaDominantRadialRayModel_orbitResidualCollapse

#print axioms completedZetaCanonicalSlopeRayModel_orbitResidualCollapse
#print axioms etaCriticalMirrorCompletedZetaDominantRadialRayModel_orbitResidualCollapse
#print axioms riemannHypothesis_of_completedZetaDominantRadialRayModelApproximation

end DkMath.RH.CFBRCProjection
