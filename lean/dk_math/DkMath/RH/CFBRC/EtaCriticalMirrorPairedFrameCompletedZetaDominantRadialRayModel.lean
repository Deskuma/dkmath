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
Unit normalization of the nonzero canonical completed-zeta slope direction.

The positive real normalization changes neither the represented real line nor
its projective phase, but removes an otherwise spurious derivative-norm factor
from radial comparisons with the eta endpoint.
-/
noncomputable def completedZetaCanonicalSlopeUnitDirection
    (s : ℂ) : ℂ :=
  completedZetaCanonicalSlopeDirection s *
    (((‖completedZetaCanonicalSlopeDirection s‖)⁻¹ : ℝ) : ℂ)

/-- The normalized completed-zeta slope direction has unit norm. -/
theorem norm_completedZetaCanonicalSlopeUnitDirection
    (s : ℂ) :
    ‖completedZetaCanonicalSlopeUnitDirection s‖ = 1 := by
  have hdirection : completedZetaCanonicalSlopeDirection s ≠ 0 :=
    completedZetaCanonicalSlopeDirection_ne_zero s
  have hnorm : ‖completedZetaCanonicalSlopeDirection s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdirection
  simp [completedZetaCanonicalSlopeUnitDirection, hnorm]

/-- The unit-normalized completed-zeta slope direction remains nonzero. -/
theorem completedZetaCanonicalSlopeUnitDirection_ne_zero
    (s : ℂ) :
    completedZetaCanonicalSlopeUnitDirection s ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  simp [norm_completedZetaCanonicalSlopeUnitDirection] at hnorm

/--
A unit-normalized completed-zeta slope ray with an arbitrary real amplitude.

The direction is supplied entirely by completed zeta.  The amplitude may depend
on the truncation index and the observation point, but remains real, so every
value lies exactly on the fixed projective line selected by the canonical
completed-zeta slope direction.  Unit normalization makes the model norm equal
to the absolute radial amplitude.
-/
noncomputable def completedZetaCanonicalSlopeRayModel
    (amplitude : ℕ → ℂ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  completedZetaCanonicalSlopeUnitDirection s *
    ((amplitude k s : ℝ) : ℂ)

/-- Every real-amplitude slope-ray value has zero completed-zeta line defect. -/
theorem completedZetaCanonicalSlopeRayModel_realLineDefect_eq_zero
    (amplitude : ℕ → ℂ → ℝ) (k : ℕ) (s : ℂ) :
    complexRealLineDefect
        (completedZetaCanonicalSlopeDirection s)
        (completedZetaCanonicalSlopeRayModel amplitude k s) = 0 := by
  have hdirection : completedZetaCanonicalSlopeDirection s ≠ 0 :=
    completedZetaCanonicalSlopeDirection_ne_zero s
  unfold complexRealLineDefect
  unfold completedZetaCanonicalSlopeRayModel
  unfold completedZetaCanonicalSlopeUnitDirection
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [inv_mul_cancel₀ hdirection]
  simp

/-- The norm of a slope-ray value is exactly the absolute radial amplitude. -/
theorem norm_completedZetaCanonicalSlopeRayModel
    (amplitude : ℕ → ℂ → ℝ) (k : ℕ) (s : ℂ) :
    ‖completedZetaCanonicalSlopeRayModel amplitude k s‖ =
      |amplitude k s| := by
  unfold completedZetaCanonicalSlopeRayModel
  rw [norm_mul, norm_completedZetaCanonicalSlopeUnitDirection]
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
    simp [completedZetaCanonicalSlopeRayModel_realLineDefect_eq_zero,
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))]
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
coefficient, while its unit direction is the fixed canonical completed-zeta
slope ray.  It does not inspect or copy the endpoint carrier.
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

#print axioms norm_completedZetaCanonicalSlopeUnitDirection
#print axioms completedZetaCanonicalSlopeRayModel_orbitResidualCollapse
#print axioms etaCriticalMirrorCompletedZetaDominantRadialRayModel_orbitResidualCollapse
#print axioms riemannHypothesis_of_completedZetaDominantRadialRayModelApproximation

end DkMath.RH.CFBRCProjection
