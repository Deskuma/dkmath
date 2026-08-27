/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaTailReduction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionCore
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailPhaseLock"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology

/--
The moving projective coefficient obtained by combining the fixed
completed-zeta slope phase with the square of the pair-left base rotation.
-/
noncomputable def etaCriticalMirrorCompletedZetaTailMovingPhase
    (k : ℕ) (s : ℂ) : ℂ :=
  completedZetaCanonicalSlopeProjectivePhase s *
    etaPairBaseRotation s k * etaPairBaseRotation s k

/--
On the nonreal zero locus, the weighted complete-tail residual is exactly the
completed-zeta projective phase residual of the dominant endpoint carrier.
-/
theorem etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual_eq_endpointPhaseResidual_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual k s =
      etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
        completedZetaCanonicalSlopeProjectivePhase s *
          conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s) := by
  rw [←
    etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidual_eq_tailOrbitResidual_of_zero
      hs him k]
  rw [←
    etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual_eq_indexPower_mul_unweighted]
  rw [←
    etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual_eq_finiteEtaOrbitResidual]
  unfold etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual
  rw [etaCriticalMirrorDominantNormalizedEndpointCarrier_conj]

/--
Exact collision algebra: subtracting the fixed completed-zeta phase residual
from the phase-scaled local pair-frame residual factors by the moving phase
coefficient minus one.
-/
theorem etaCriticalMirrorCompletedZetaTail_phaseCollision_factor
    (k : ℕ) (s : ℂ) :
    completedZetaCanonicalSlopeProjectivePhase s *
          (etaPairBaseRotation s k * etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)) -
        (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
          completedZetaCanonicalSlopeProjectivePhase s *
            conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)) =
      (etaCriticalMirrorCompletedZetaTailMovingPhase k s - 1) *
        etaCriticalMirrorDominantNormalizedEndpointCarrier k s := by
  unfold etaCriticalMirrorCompletedZetaTailMovingPhase
  ring

/--
Collapse of the dominant-weighted complete-tail residual forces the fixed
completed-zeta projective phase to lock to the squared moving pair-left frame.
This is the explicit phase-lock output consumed by the two-scale obstruction.
-/
theorem etaCriticalMirrorCompletedZetaTailMovingPhase_tendsto_one_of_residualCollapse
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ => etaCriticalMirrorCompletedZetaTailMovingPhase k s)
      atTop (nhds 1) := by
  have hglobalTail := htail hs him
  have hglobalPhaseResidual :
      Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            completedZetaCanonicalSlopeProjectivePhase s *
              conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s))
        atTop (nhds 0) := by
    refine hglobalTail.congr' (Eventually.of_forall fun k => ?_)
    exact
      etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual_eq_endpointPhaseResidual_of_zero
        hs him k
  have hlocalIm :
      Tendsto
        (fun k : ℕ =>
          (etaPairBaseRotation s k *
            etaCriticalMirrorDominantNormalizedEndpointCarrier k s).im)
        atTop (nhds 0) := by
    simpa only [etaPairMovingRealLineDefect, complexRealAxisDefect] using
      etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock
        hs him hre
  have hlocalTwice :
      Tendsto
        (fun k : ℕ =>
          2 *
            (etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s).im)
        atTop (nhds 0) := by
    simpa using hlocalIm.const_mul 2
  have hlocalCast :
      Tendsto
        (fun k : ℕ =>
          ((2 *
              (etaPairBaseRotation s k *
                etaCriticalMirrorDominantNormalizedEndpointCarrier k s).im : ℝ) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hlocalTwice
    simpa [Function.comp_def] using h
  have hlocalSkew :
      Tendsto
        (fun k : ℕ =>
          etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            conj
              (etaPairBaseRotation s k *
                etaCriticalMirrorDominantNormalizedEndpointCarrier k s))
        atTop (nhds 0) := by
    have h := hlocalCast.mul_const Complex.I
    have h' :
        Tendsto
          (fun k : ℕ =>
            ((2 *
                (etaPairBaseRotation s k *
                  etaCriticalMirrorDominantNormalizedEndpointCarrier k s).im : ℝ) : ℂ) *
              Complex.I)
          atTop (nhds 0) := by
      simpa using h
    refine h'.congr' (Eventually.of_forall fun k => ?_)
    simpa using
      (Complex.sub_conj
        (etaPairBaseRotation s k *
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s)).symm
  have hlocalRotatedSkew :
      Tendsto
        (fun k : ℕ =>
          etaPairBaseRotation s k *
            (etaPairBaseRotation s k *
                etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              conj
                (etaPairBaseRotation s k *
                  etaCriticalMirrorDominantNormalizedEndpointCarrier k s)))
        atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hlocalSkew
    refine hnorm.congr' (Eventually.of_forall fun k => ?_)
    simp only [sub_zero, norm_mul, norm_etaPairBaseRotation, one_mul]
  have hlocalPhaseResidual :
      Tendsto
        (fun k : ℕ =>
          etaPairBaseRotation s k * etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s))
        atTop (nhds 0) := by
    refine hlocalRotatedSkew.congr' (Eventually.of_forall fun k => ?_)
    rw [map_mul]
    calc
      etaPairBaseRotation s k *
          (etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            conj (etaPairBaseRotation s k) *
              conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)) =
        etaPairBaseRotation s k * etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
          (etaPairBaseRotation s k * conj (etaPairBaseRotation s k)) *
            conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s) := by
        ring
      _ =
        etaPairBaseRotation s k * etaPairBaseRotation s k *
              etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
          conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s) := by
        rw [etaPairBaseRotation_mul_conj_eq_one, one_mul]
  have hphaseLocalResidual :
      Tendsto
        (fun k : ℕ =>
          completedZetaCanonicalSlopeProjectivePhase s *
            (etaPairBaseRotation s k * etaPairBaseRotation s k *
                etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto
          (fun _ : ℕ => completedZetaCanonicalSlopeProjectivePhase s)
          atTop (nhds (completedZetaCanonicalSlopeProjectivePhase s)) from
        tendsto_const_nhds).mul hlocalPhaseResidual
  have hcoefficientProduct :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorCompletedZetaTailMovingPhase k s - 1) *
            etaCriticalMirrorDominantNormalizedEndpointCarrier k s)
        atTop (nhds 0) := by
    have hsum := hphaseLocalResidual.add hglobalPhaseResidual.neg
    have hsum' :
        Tendsto
          (fun k : ℕ =>
            completedZetaCanonicalSlopeProjectivePhase s *
                (etaPairBaseRotation s k * etaPairBaseRotation s k *
                    etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
                  conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)) -
              (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
                completedZetaCanonicalSlopeProjectivePhase s *
                  conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)))
          atTop (nhds 0) := by
      simpa only [sub_eq_add_neg, add_zero, neg_zero] using hsum
    refine hsum'.congr' (Eventually.of_forall fun k => ?_)
    exact etaCriticalMirrorCompletedZetaTail_phaseCollision_factor k s
  rcases
      etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse
        hs him hre with
    ⟨c, hc, hlower⟩
  exact
    tendsto_one_of_mul_sub_one_tendsto_zero_of_eventually_norm_lower_bound
      hc hcoefficientProduct hlower

/--
Ultra collision: the extracted completed-zeta phase lock would make both
positive-density relative-frame limits projectively trivial, contradicting
two-scale nonresonance at every nonzero imaginary height.
-/
theorem etaCriticalMirror_re_eq_half_of_completedZetaWeightedTailOrbitResidualCollapse
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  have hphase :=
    etaCriticalMirrorCompletedZetaTailMovingPhase_tendsto_one_of_residualCollapse
      htail hs him hre
  have hhalf :
      EtaPairProjectiveUnitRotation
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s) :=
    scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
      etaPairHalfDensityBlockSchedule s
      (completedZetaCanonicalSlopeProjectivePhase s) hphase
  have hfull :
      EtaPairProjectiveUnitRotation
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s) :=
    scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
      etaPairFullDensityBlockSchedule s
      (completedZetaCanonicalSlopeProjectivePhase s) hphase
  rcases
      etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
        him with hhalfNe | hfullNe
  · exact hhalfNe hhalf
  · exact hfullNe hfull

/-- RH follows through the explicit completed-zeta tail phase-lock collision. -/
theorem riemannHypothesis_of_completedZetaWeightedTailPhaseLockCollision
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  exact
    etaCriticalMirror_re_eq_half_of_completedZetaWeightedTailOrbitResidualCollapse
      htail hs (nontrivialRiemannZetaZero_im_ne_zero hs)

#print axioms etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual_eq_endpointPhaseResidual_of_zero
#print axioms etaCriticalMirrorCompletedZetaTailMovingPhase_tendsto_one_of_residualCollapse
#print axioms etaCriticalMirror_re_eq_half_of_completedZetaWeightedTailOrbitResidualCollapse
#print axioms riemannHypothesis_of_completedZetaWeightedTailPhaseLockCollision

end DkMath.RH.CFBRCProjection
