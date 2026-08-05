/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseRelativePhase
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionCore
import DkMath.RH.CFBRC.StandardZetaRealAxisClosure
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRelativePhaseCollision"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology

/-- Real logarithmic angle of the pair-left counter-rotation. -/
noncomputable def etaPairLogarithmicCounterPhase
    (k : ℕ) (s : ℂ) : ℝ :=
  -(s.im * Real.log (etaPairFrameLeftEndpoint k))

/-- The relative counter-rotation is one fixed completed-zeta factor times the explicit logarithmic rotation. -/
theorem etaCriticalMirrorCompletedZetaRelativeCounterRotation_eq_fixed_mul_exp
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorCompletedZetaRelativeCounterRotation k s =
      (completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
        Complex.exp
          (Complex.I * (((etaPairLogarithmicCounterPhase k s : ℝ) : ℂ))) := by
  unfold etaCriticalMirrorCompletedZetaRelativeCounterRotation
  unfold etaPairBaseCounterRotation
  unfold etaPairBaseRotation
  unfold etaPairLogarithmicCounterPhase
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- A unit-complex sequence whose imaginary part tends to zero has square tending to one. -/
theorem tendsto_mul_self_one_of_norm_eq_one_of_im_tendsto_zero
    {q : ℕ → ℂ}
    (hnorm : ∀ k : ℕ, ‖q k‖ = 1)
    (him : Tendsto (fun k : ℕ => (q k).im) atTop (nhds 0)) :
    Tendsto (fun k : ℕ => q k * q k) atTop (nhds 1) := by
  have htwice :
      Tendsto (fun k : ℕ => 2 * (q k).im) atTop (nhds 0) := by
    simpa using him.const_mul 2
  have hcast :
      Tendsto
        (fun k : ℕ => ((2 * (q k).im : ℝ) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp htwice
    simpa [Function.comp_def] using h
  have hskew :
      Tendsto (fun k : ℕ => q k - conj (q k)) atTop (nhds 0) := by
    have h := hcast.mul_const Complex.I
    have h' :
        Tendsto
          (fun k : ℕ => ((2 * (q k).im : ℝ) : ℂ) * Complex.I)
          atTop (nhds 0) := by
      simpa using h
    refine h'.congr' (Eventually.of_forall fun k => ?_)
    simpa using (Complex.sub_conj (q k)).symm
  have hproduct :
      Tendsto
        (fun k : ℕ => q k * (q k - conj (q k)))
        atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnormSkew := tendsto_iff_norm_sub_tendsto_zero.mp hskew
    refine hnormSkew.congr' (Eventually.of_forall fun k => ?_)
    simp only [sub_zero, norm_mul, hnorm, one_mul]
  have hsub :
      Tendsto (fun k : ℕ => q k * q k - 1) atTop (nhds 0) := by
    refine hproduct.congr' (Eventually.of_forall fun k => ?_)
    have hunit : q k * conj (q k) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm k]
      norm_num
    rw [mul_sub, hunit]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnormSub := tendsto_iff_norm_sub_tendsto_zero.mp hsub
  simpa only [sub_zero] using hnormSub

/-- Fixed completed-zeta square phase used to compare the pair-left moving gauges. -/
noncomputable def completedZetaCanonicalSlopeUnitSquarePhase
    (s : ℂ) : ℂ :=
  completedZetaCanonicalSlopeUnitDirection s *
    completedZetaCanonicalSlopeUnitDirection s

/-- Imaginary relative-phase collapse forces a fixed-phase square lock on the pair-left rotations. -/
theorem completedZetaCanonicalSlopeUnitSquarePhase_mul_baseRotation_sq_tendsto_one_of_relativePhase_im_tendsto_zero
    {s : ℂ}
    (hphase :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im)
        atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ =>
        completedZetaCanonicalSlopeUnitSquarePhase s *
          etaPairBaseRotation s k * etaPairBaseRotation s k)
      atTop (nhds 1) := by
  have hsq :
      Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorCompletedZetaRelativeCounterRotation k s *
            etaCriticalMirrorCompletedZetaRelativeCounterRotation k s)
        atTop (nhds 1) :=
    tendsto_mul_self_one_of_norm_eq_one_of_im_tendsto_zero
      (fun k => norm_etaCriticalMirrorCompletedZetaRelativeCounterRotation k s)
      hphase
  have hinv :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s *
            etaCriticalMirrorCompletedZetaRelativeCounterRotation k s)⁻¹)
        atTop (nhds 1) := by
    simpa using hsq.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  refine hinv.congr' (Eventually.of_forall fun k => ?_)
  have hu : completedZetaCanonicalSlopeUnitDirection s ≠ 0 :=
    completedZetaCanonicalSlopeUnitDirection_ne_zero s
  have hrotation : etaPairBaseRotation s k ≠ 0 :=
    etaPairBaseRotation_ne_zero s k
  unfold etaCriticalMirrorCompletedZetaRelativeCounterRotation
  unfold completedZetaCanonicalSlopeUnitSquarePhase
  unfold etaPairBaseCounterRotation
  field_simp [hu, hrotation]
  ring

/-- At every nonzero height, the relative completed-zeta / pair-left phase cannot become asymptotically real. -/
theorem not_etaCriticalMirrorCompletedZetaRelativeCounterRotation_im_tendsto_zero
    {s : ℂ} (him : s.im ≠ 0) :
    ¬ Tendsto
      (fun k : ℕ =>
        (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im)
      atTop (nhds 0) := by
  intro hphase
  have hsquare :=
    completedZetaCanonicalSlopeUnitSquarePhase_mul_baseRotation_sq_tendsto_one_of_relativePhase_im_tendsto_zero
      hphase
  have hhalf :
      EtaPairProjectiveUnitRotation
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s) :=
    scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
      etaPairHalfDensityBlockSchedule s
      (completedZetaCanonicalSlopeUnitSquarePhase s) hsquare
  have hfull :
      EtaPairProjectiveUnitRotation
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s) :=
    scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
      etaPairFullDensityBlockSchedule s
      (completedZetaCanonicalSlopeUnitSquarePhase s) hsquare
  rcases
      etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
        him with hhalfNe | hfullNe
  · exact hhalfNe hhalf
  · exact hfullNe hfull

/-- The relative-phase lock contract excludes every off-critical nontrivial zero. -/
theorem etaCriticalMirror_re_eq_half_of_completedZetaRelativePhaseImagCollapse
    (hphase : EtaCriticalMirrorCompletedZetaRelativePhaseImagCollapse)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  exact
    not_etaCriticalMirrorCompletedZetaRelativeCounterRotation_im_tendsto_zero him
      (hphase hs him hre)

/-- The minimal off-critical relative logarithmic phase-lock contract implies RH. -/
theorem riemannHypothesis_of_completedZetaRelativePhaseImagCollapse
    (hphase : EtaCriticalMirrorCompletedZetaRelativePhaseImagCollapse) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  exact
    etaCriticalMirror_re_eq_half_of_completedZetaRelativePhaseImagCollapse
      hphase hs (nontrivialRiemannZetaZero_im_ne_zero hs)

#print axioms etaCriticalMirrorCompletedZetaRelativeCounterRotation_eq_fixed_mul_exp
#print axioms tendsto_mul_self_one_of_norm_eq_one_of_im_tendsto_zero
#print axioms not_etaCriticalMirrorCompletedZetaRelativeCounterRotation_im_tendsto_zero
#print axioms riemannHypothesis_of_completedZetaRelativePhaseImagCollapse

end DkMath.RH.CFBRCProjection
