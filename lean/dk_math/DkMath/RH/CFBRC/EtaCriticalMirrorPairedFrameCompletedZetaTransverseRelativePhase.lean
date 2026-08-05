/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialTransverseDecomposition
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTransverseRelativePhase"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- The dominant endpoint transported into its local pair-left real frame. -/
noncomputable def etaCriticalMirrorDominantLocalRotatedCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaPairBaseRotation s k *
    etaCriticalMirrorDominantNormalizedEndpointCarrier k s

/--
Relative counter-rotation from the local pair-left frame to the fixed
unit-normalized completed-zeta slope frame.
-/
noncomputable def etaCriticalMirrorCompletedZetaRelativeCounterRotation
    (k : ℕ) (s : ℂ) : ℂ :=
  (completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
    etaPairBaseCounterRotation s k

/-- The completed-zeta / pair-left relative counter-rotation has unit norm. -/
theorem norm_etaCriticalMirrorCompletedZetaRelativeCounterRotation
    (k : ℕ) (s : ℂ) :
    ‖etaCriticalMirrorCompletedZetaRelativeCounterRotation k s‖ = 1 := by
  unfold etaCriticalMirrorCompletedZetaRelativeCounterRotation
  rw [norm_mul, norm_inv,
    norm_completedZetaCanonicalSlopeUnitDirection,
    norm_etaPairBaseCounterRotation, inv_one, one_mul]

/--
The completed-zeta unit coordinate of the endpoint factors exactly into the
relative counter-rotation and the local rotated carrier.
-/
theorem etaCriticalMirrorCompletedZetaUnitCoordinate_eq_relativeCounterRotation_mul_localCarrier
    (k : ℕ) (s : ℂ) :
    completedZetaCanonicalSlopeUnitCoordinate s
        (etaCriticalMirrorDominantNormalizedEndpointCarrier k s) =
      etaCriticalMirrorCompletedZetaRelativeCounterRotation k s *
        etaCriticalMirrorDominantLocalRotatedCarrier k s := by
  unfold completedZetaCanonicalSlopeUnitCoordinate
  unfold etaCriticalMirrorCompletedZetaRelativeCounterRotation
  unfold etaCriticalMirrorDominantLocalRotatedCarrier
  symm
  calc
    ((completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
          etaPairBaseCounterRotation s k) *
        (etaPairBaseRotation s k *
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s) =
      (completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
        (etaPairBaseCounterRotation s k * etaPairBaseRotation s k) *
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s := by
            ring
    _ =
      (completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
        etaCriticalMirrorDominantNormalizedEndpointCarrier k s := by
          rw [etaPairBaseCounterRotation_mul_baseRotation, mul_one]

/--
Exact transverse phase formula.  The fixed-line transverse coordinate is the
imaginary part of the relative counter-rotation acting on the local carrier.
-/
theorem etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s =
      (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s *
        etaCriticalMirrorDominantLocalRotatedCarrier k s).im := by
  unfold etaCriticalMirrorCompletedZetaDominantTransverseCoordinate
  unfold completedZetaCanonicalSlopeTransverseCoordinate
  rw [
    etaCriticalMirrorCompletedZetaUnitCoordinate_eq_relativeCounterRotation_mul_localCarrier]

/--
Real/imaginary expansion of the transverse phase formula.
-/
theorem etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase_split
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s =
      (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).re *
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).im +
        (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im *
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).re := by
  rw [etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase]
  rw [Complex.mul_im]

/-- A uniformly unit-bounded real coefficient preserves convergence to zero. -/
private theorem tendsto_zero_of_abs_le_one_mul
    {x y : ℕ → ℝ}
    (hx : ∀ k : ℕ, |x k| ≤ 1)
    (hy : Tendsto y atTop (nhds 0)) :
    Tendsto (fun k : ℕ => x k * y k) atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hynorm := tendsto_iff_norm_sub_tendsto_zero.mp hy
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hynorm
      (Eventually.of_forall fun k => norm_nonneg (x k * y k - 0))
      (Eventually.of_forall fun k => ?_)
  simp only [sub_zero, Real.norm_eq_abs, abs_mul]
  calc
    |x k| * |y k| ≤ 1 * |y k| :=
      mul_le_mul_of_nonneg_right (hx k) (abs_nonneg _)
    _ = |y k| := one_mul _

/--
At every nonreal off-critical zero, the local rotated dominant carrier tends to
one nonzero real eta half-tail constant.
-/
theorem etaCriticalMirrorDominantLocalRotatedCarrier_exists_real_nonzero_limit
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    ∃ L : ℂ,
      L.im = 0 ∧
      L.re ≠ 0 ∧
      Tendsto
        (fun k : ℕ => etaCriticalMirrorDominantLocalRotatedCarrier k s)
        atTop (nhds L) := by
  rcases lt_or_gt_of_ne hre with hleft | hright
  · let L : ℂ := etaPairIndexNormalizedTailConstant s
    have hLim : L.im = 0 := by
      simp [L, etaPairIndexNormalizedTailConstant]
    have hLne : L ≠ 0 := by
      exact etaPairIndexNormalizedTailConstant_ne_zero s
    have hLre : L.re ≠ 0 := by
      intro hzero
      apply hLne
      apply Complex.ext
      · simpa using hzero
      · simpa using hLim
    refine ⟨L, hLim, hLre, ?_⟩
    have hrotated :=
      (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hleft).rotated_endpoint_tendsto
    have hle : s.re ≤ (1 : ℝ) / 2 := le_of_lt hleft
    have hle' : s.re ≤ 2⁻¹ := by simpa using hle
    simpa [etaCriticalMirrorDominantLocalRotatedCarrier,
      etaCriticalMirrorDominantNormalizedEndpointCarrier,
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint,
      L, hle, hle'] using hrotated
  · let L : ℂ := -etaPairIndexNormalizedTailConstant (criticalMirror s)
    have hLim : L.im = 0 := by
      simp [L, etaPairIndexNormalizedTailConstant]
    have hLne : L ≠ 0 := by
      exact neg_ne_zero.mpr
        (etaPairIndexNormalizedTailConstant_ne_zero (criticalMirror s))
    have hLre : L.re ≠ 0 := by
      intro hzero
      apply hLne
      apply Complex.ext
      · simpa using hzero
      · simpa using hLim
    refine ⟨L, hLim, hLre, ?_⟩
    have hrotated :=
      (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hright).rotated_endpoint_tendsto
    have hnotle : ¬ s.re ≤ (1 : ℝ) / 2 := not_le.mpr hright
    have hnotle' : ¬ s.re ≤ 2⁻¹ := by simpa using hnotle
    simpa [etaCriticalMirrorDominantLocalRotatedCarrier,
      etaCriticalMirrorDominantNormalizedEndpointCarrier,
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint,
      L, hnotle, hnotle'] using hrotated

/--
At a hypothetical off-critical zero, transverse collapse is equivalent to the
relative completed-zeta / pair-left counter-rotation becoming asymptotically
real.  The nonzero real local-carrier limit is what allows the phase coefficient
to be separated from the endpoint.
-/
theorem etaCriticalMirrorCompletedZetaDominantTransverse_tendsto_zero_iff_relativePhase_im_tendsto_zero
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s)
        atTop (nhds 0) ↔
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im)
        atTop (nhds 0) := by
  rcases
      etaCriticalMirrorDominantLocalRotatedCarrier_exists_real_nonzero_limit
        hs him hre with
    ⟨L, hLim, hLre, hlocal⟩
  have hlocalRe :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).re)
        atTop (nhds L.re) := by
    have h := (Complex.continuous_re.tendsto L).comp hlocal
    simpa [Function.comp_def] using h
  have hlocalIm :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).im)
        atTop (nhds 0) := by
    have h := (Complex.continuous_im.tendsto L).comp hlocal
    simpa [Function.comp_def, hLim] using h
  have hqReBound :
      ∀ k : ℕ,
        |(etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).re| ≤ 1 := by
    intro k
    calc
      |(etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).re| ≤
          ‖etaCriticalMirrorCompletedZetaRelativeCounterRotation k s‖ :=
        Complex.abs_re_le_norm _
      _ = 1 :=
        norm_etaCriticalMirrorCompletedZetaRelativeCounterRotation k s
  have hfirst :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).re *
            (etaCriticalMirrorDominantLocalRotatedCarrier k s).im)
        atTop (nhds 0) :=
    tendsto_zero_of_abs_le_one_mul hqReBound hlocalIm
  constructor
  · intro htransverse
    have hsecond :
        Tendsto
          (fun k : ℕ =>
            (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im *
              (etaCriticalMirrorDominantLocalRotatedCarrier k s).re)
          atTop (nhds 0) := by
      have hdiff := htransverse.sub hfirst
      have hdiff' :
          Tendsto
            (fun k : ℕ =>
              etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s -
                (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).re *
                  (etaCriticalMirrorDominantLocalRotatedCarrier k s).im)
            atTop (nhds 0) := by
        simpa using hdiff
      refine hdiff'.congr' (Eventually.of_forall fun k => ?_)
      rw [
        etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase_split]
      ring
    have hlocalReNe :
        ∀ᶠ k : ℕ in atTop,
          (etaCriticalMirrorDominantLocalRotatedCarrier k s).re ≠ 0 := by
      have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hlocalRe
      have hclose := hnorm.eventually_lt_const (norm_pos_iff.mpr hLre)
      filter_upwards [hclose] with k hk
      intro hzero
      rw [hzero, zero_sub, norm_neg] at hk
      exact (lt_irrefl _ hk)
    have hinv := hlocalRe.inv₀ hLre
    have hquot := hsecond.mul hinv
    refine hquot.congr' ?_
    filter_upwards [hlocalReNe] with k hk
    rw [mul_assoc, mul_inv_cancel₀ hk, mul_one]
  · intro hphase
    have hsecond :
        Tendsto
          (fun k : ℕ =>
            (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im *
              (etaCriticalMirrorDominantLocalRotatedCarrier k s).re)
          atTop (nhds 0) := by
      simpa only [zero_mul] using hphase.mul hlocalRe
    have hsum := hfirst.add hsecond
    refine hsum.congr' (Eventually.of_forall fun k => ?_)
    exact
      (etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase_split
        k s).symm

/--
Off-critical relative-phase lock contract.  It is pointwise equivalent to the
transverse Gap at every hypothetical off-critical nontrivial zero.
-/
def EtaCriticalMirrorCompletedZetaRelativePhaseImagCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    s.re ≠ (1 : ℝ) / 2 →
    Tendsto
      (fun k : ℕ =>
        (etaCriticalMirrorCompletedZetaRelativeCounterRotation k s).im)
      atTop (nhds 0)

/-- The current transverse-collapse contract implies off-critical relative-phase lock. -/
theorem etaCriticalMirrorCompletedZetaRelativePhaseImagCollapse_of_transverseCollapse
    (htransverse :
      EtaCriticalMirrorCompletedZetaDominantTransverseCollapse) :
    EtaCriticalMirrorCompletedZetaRelativePhaseImagCollapse := by
  intro s hs him hre
  exact
    (etaCriticalMirrorCompletedZetaDominantTransverse_tendsto_zero_iff_relativePhase_im_tendsto_zero
      hs him hre).mp
      (htransverse hs him)

#print axioms etaCriticalMirrorCompletedZetaUnitCoordinate_eq_relativeCounterRotation_mul_localCarrier
#print axioms etaCriticalMirrorCompletedZetaDominantTransverseCoordinate_eq_relativePhase_split
#print axioms etaCriticalMirrorDominantLocalRotatedCarrier_exists_real_nonzero_limit
#print axioms etaCriticalMirrorCompletedZetaDominantTransverse_tendsto_zero_iff_relativePhase_im_tendsto_zero
#print axioms etaCriticalMirrorCompletedZetaRelativePhaseImagCollapse_of_transverseCollapse

end DkMath.RH.CFBRCProjection
