/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeCompatibilityAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameConjugationAsymptoticAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSameTruncationOrbit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology

/-- Projective phase of a nonzero complex direction. -/
noncomputable def complexRealLineProjectivePhase
    (direction : ℂ) : ℂ :=
  direction * (conj direction)⁻¹

/--
The projective phase residual is the direction-scaled conjugation skew in the
coordinate frame of the selected real line.
-/
theorem complexRealLine_direction_mul_skew_eq_phaseResidual
    {direction z : ℂ} (hdirection : direction ≠ 0) :
    direction *
        (direction⁻¹ * z - conj (direction⁻¹ * z)) =
      z - complexRealLineProjectivePhase direction * conj z := by
  unfold complexRealLineProjectivePhase
  rw [map_mul, map_inv₀, mul_sub]
  rw [← mul_assoc direction direction⁻¹ z,
    mul_inv_cancel₀ hdirection, one_mul]
  rw [← mul_assoc direction (conj direction)⁻¹ (conj z)]

/-- A real-line defect tending to zero forces the projective phase residual to zero. -/
theorem tendsto_phaseResidual_zero_of_complexRealLineDefect_tendsto_zero
    {direction : ℂ} (hdirection : direction ≠ 0)
    {z : ℕ → ℂ}
    (hline :
      Tendsto
        (fun k : ℕ => complexRealLineDefect direction (z k))
        atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ =>
        z k - complexRealLineProjectivePhase direction * conj (z k))
      atTop (nhds 0) := by
  have htwice :
      Tendsto
        (fun k : ℕ => 2 * complexRealLineDefect direction (z k))
        atTop (nhds 0) := by
    simpa using hline.const_mul 2
  have hcast :
      Tendsto
        (fun k : ℕ =>
          ((2 * complexRealLineDefect direction (z k) : ℝ) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp htwice
    simpa [Function.comp_def] using h
  have hskew :
      Tendsto
        (fun k : ℕ =>
          direction⁻¹ * z k - conj (direction⁻¹ * z k))
        atTop (nhds 0) := by
    have h := hcast.mul_const Complex.I
    have h' :
        Tendsto
          (fun k : ℕ =>
            ((2 * complexRealLineDefect direction (z k) : ℝ) : ℂ) *
              Complex.I)
          atTop (nhds 0) := by
      simpa using h
    refine h'.congr' (Eventually.of_forall fun k => ?_)
    simpa [complexRealLineDefect] using
      (Complex.sub_conj (direction⁻¹ * z k)).symm
  have hrotated :
      Tendsto
        (fun k : ℕ =>
          direction *
            (direction⁻¹ * z k - conj (direction⁻¹ * z k)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun _ : ℕ => direction) atTop (nhds direction) from
        tendsto_const_nhds).mul hskew
  refine hrotated.congr' (Eventually.of_forall fun k => ?_)
  exact
    complexRealLine_direction_mul_skew_eq_phaseResidual hdirection

/-- A vanishing projective phase residual forces the corresponding real-line defect to zero. -/
theorem complexRealLineDefect_tendsto_zero_of_tendsto_phaseResidual_zero
    {direction : ℂ} (hdirection : direction ≠ 0)
    {z : ℕ → ℂ}
    (hresidual :
      Tendsto
        (fun k : ℕ =>
          z k - complexRealLineProjectivePhase direction * conj (z k))
        atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ => complexRealLineDefect direction (z k))
      atTop (nhds 0) := by
  have hrotated :
      Tendsto
        (fun k : ℕ =>
          direction⁻¹ *
            (z k - complexRealLineProjectivePhase direction * conj (z k)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun _ : ℕ => direction⁻¹) atTop (nhds direction⁻¹) from
        tendsto_const_nhds).mul hresidual
  have hskew :
      Tendsto
        (fun k : ℕ =>
          direction⁻¹ * z k - conj (direction⁻¹ * z k))
        atTop (nhds 0) := by
    refine hrotated.congr' (Eventually.of_forall fun k => ?_)
    rw [← complexRealLine_direction_mul_skew_eq_phaseResidual
      hdirection]
    rw [← mul_assoc, inv_mul_cancel₀ hdirection, one_mul]
  have himaginary :=
    (Complex.continuous_im.tendsto 0).comp hskew
  have himaginary' :
      Tendsto
        (fun k : ℕ =>
          (direction⁻¹ * z k - conj (direction⁻¹ * z k)).im)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using himaginary
  have htwice :
      Tendsto
        (fun k : ℕ =>
          2 * complexRealLineDefect direction (z k))
        atTop (nhds 0) := by
    refine himaginary'.congr' (Eventually.of_forall fun k => ?_)
    simp [complexRealLineDefect]
    ring
  have hhalf := htwice.const_mul ((1 : ℝ) / 2)
  have hhalf' :
      Tendsto
        (fun k : ℕ =>
          ((1 : ℝ) / 2) *
            (2 * complexRealLineDefect direction (z k)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using hhalf
  refine hhalf'.congr' (Eventually.of_forall fun k => ?_)
  ring

/-- The side-aware dominant endpoint commutes exactly with conjugation. -/
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_conj
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorDominantNormalizedEndpointCarrier k (conj s) =
      conj (etaCriticalMirrorDominantNormalizedEndpointCarrier k s) := by
  by_cases hside : s.re ≤ (1 : ℝ) / 2
  · simp [etaCriticalMirrorDominantNormalizedEndpointCarrier, hside,
      etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_conj]
  · simp [etaCriticalMirrorDominantNormalizedEndpointCarrier, hside,
      criticalMirror_conj,
      etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_conj]

/-- Fixed projective phase selected by the completed-zeta slope direction. -/
noncomputable def completedZetaCanonicalSlopeProjectivePhase
    (s : ℂ) : ℂ :=
  complexRealLineProjectivePhase
    (completedZetaCanonicalSlopeDirection s)

/--
Same-truncation conjugation-orbit residual for the dominant eta endpoint.
Both endpoint terms use the same finite index `k`; the fixed projective phase
comes from completed zeta and is independent of `k`.
-/
noncomputable def etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
    completedZetaCanonicalSlopeProjectivePhase s *
      etaCriticalMirrorDominantNormalizedEndpointCarrier k (conj s)

/-- The explicit same-truncation orbit condition replacing geometric line notation. -/
def EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual k s)
      atTop (nhds 0)

/-- Same-truncation orbit collapse is exactly the completed-zeta slope line condition. -/
theorem etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_lineCompatibility :
    EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility := by
  constructor
  · intro horbit s hs him
    have hresidual := horbit hs him
    have hresidual' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              completedZetaCanonicalSlopeProjectivePhase s *
                conj
                  (etaCriticalMirrorDominantNormalizedEndpointCarrier k s))
          atTop (nhds 0) := by
      refine hresidual.congr' (Eventually.of_forall fun k => ?_)
      simp [etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual,
        etaCriticalMirrorDominantNormalizedEndpointCarrier_conj]
    exact
      complexRealLineDefect_tendsto_zero_of_tendsto_phaseResidual_zero
        (completedZetaCanonicalSlopeDirection_ne_zero s)
        (by
          simpa [completedZetaCanonicalSlopeProjectivePhase] using
            hresidual')
  · intro hline s hs him
    have hresidual :=
      tendsto_phaseResidual_zero_of_complexRealLineDefect_tendsto_zero
        (completedZetaCanonicalSlopeDirection_ne_zero s)
        (hline hs him)
    refine hresidual.congr' (Eventually.of_forall fun k => ?_)
    simp [etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual,
      completedZetaCanonicalSlopeProjectivePhase,
      etaCriticalMirrorDominantNormalizedEndpointCarrier_conj]

/-- RH follows from the explicit same-index completed-zeta conjugation orbit residual. -/
theorem riemannHypothesis_of_endpointCompletedZetaSameTruncationOrbitResidualCollapse
    (horbit :
      EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSlopeLineCompatibility
    (etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_lineCompatibility.mp
      horbit)

#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_conj
#print axioms etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_lineCompatibility
#print axioms riemannHypothesis_of_endpointCompletedZetaSameTruncationOrbitResidualCollapse

end DkMath.RH.CFBRCProjection
