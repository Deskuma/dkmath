/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantRadialRayModel
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRadialTransverseDecomposition"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Coordinate of `z` in the unit-normalized completed-zeta slope frame. -/
noncomputable def completedZetaCanonicalSlopeUnitCoordinate
    (s z : ℂ) : ℂ :=
  (completedZetaCanonicalSlopeUnitDirection s)⁻¹ * z

/-- Multiplying the unit-frame coordinate by its direction reconstructs `z`. -/
theorem completedZetaCanonicalSlopeUnitDirection_mul_unitCoordinate
    (s z : ℂ) :
    completedZetaCanonicalSlopeUnitDirection s *
        completedZetaCanonicalSlopeUnitCoordinate s z = z := by
  unfold completedZetaCanonicalSlopeUnitCoordinate
  rw [← mul_assoc]
  rw [mul_inv_cancel₀ (completedZetaCanonicalSlopeUnitDirection_ne_zero s)]
  simp

/-- Every unit-frame coordinate splits into its real and imaginary components. -/
theorem completedZetaCanonicalSlopeUnitCoordinate_eq_re_add_im
    (s z : ℂ) :
    completedZetaCanonicalSlopeUnitCoordinate s z =
      ((completedZetaCanonicalSlopeUnitCoordinate s z).re : ℂ) +
        Complex.I *
          ((completedZetaCanonicalSlopeUnitCoordinate s z).im : ℂ) := by
  apply Complex.ext <;> simp

/-- Orthogonal real-line projection in the completed-zeta unit frame. -/
noncomputable def completedZetaCanonicalSlopeRealProjection
    (s z : ℂ) : ℂ :=
  completedZetaCanonicalSlopeUnitDirection s *
    ((completedZetaCanonicalSlopeUnitCoordinate s z).re : ℂ)

/-- Imaginary coordinate transverse to the completed-zeta unit line. -/
noncomputable def completedZetaCanonicalSlopeTransverseCoordinate
    (s z : ℂ) : ℝ :=
  (completedZetaCanonicalSlopeUnitCoordinate s z).im

/-- Exact orthogonal decomposition into fixed-line projection and transverse part. -/
theorem completedZetaCanonicalSlope_eq_projection_add_transverse
    (s z : ℂ) :
    z = completedZetaCanonicalSlopeRealProjection s z +
      completedZetaCanonicalSlopeUnitDirection s *
        (Complex.I *
          ((completedZetaCanonicalSlopeTransverseCoordinate s z : ℝ) : ℂ)) := by
  rw [← completedZetaCanonicalSlopeUnitDirection_mul_unitCoordinate s z]
  unfold completedZetaCanonicalSlopeRealProjection
  unfold completedZetaCanonicalSlopeTransverseCoordinate
  rw [completedZetaCanonicalSlopeUnitCoordinate_eq_re_add_im]
  ring

/-- Distance to the completed-zeta fixed line is exactly the absolute transverse coordinate. -/
theorem norm_sub_completedZetaCanonicalSlopeRealProjection
    (s z : ℂ) :
    ‖z - completedZetaCanonicalSlopeRealProjection s z‖ =
      |completedZetaCanonicalSlopeTransverseCoordinate s z| := by
  rw [completedZetaCanonicalSlope_eq_projection_add_transverse]
  ring_nf
  rw [norm_mul, norm_completedZetaCanonicalSlopeUnitDirection]
  simp [completedZetaCanonicalSlopeTransverseCoordinate]

/-- Signed radial-coordinate error against the explicit dominant ray amplitude. -/
noncomputable def etaCriticalMirrorCompletedZetaDominantRadialCoordinateError
    (k : ℕ) (s : ℂ) : ℝ :=
  (completedZetaCanonicalSlopeUnitCoordinate s
      (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)).re -
    etaCriticalMirrorDominantRadialAmplitude k s

/-- Transverse endpoint coordinate in the completed-zeta unit frame. -/
noncomputable def etaCriticalMirrorCompletedZetaDominantTransverseCoordinate
    (k : ℕ) (s : ℂ) : ℝ :=
  completedZetaCanonicalSlopeTransverseCoordinate s
    (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)

/-- Exact factorization of the endpoint-to-ray error into radial and transverse coordinates. -/
theorem etaCriticalMirrorCompletedZetaDominantEndpoint_sub_rayModel_eq
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
        etaCriticalMirrorCompletedZetaDominantRadialRayModel k s =
      completedZetaCanonicalSlopeUnitDirection s *
        (((etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s : ℝ) : ℂ) +
          Complex.I *
            ((etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s : ℝ) : ℂ)) := by
  rw [← completedZetaCanonicalSlopeUnitDirection_mul_unitCoordinate s
    (etaCriticalMirrorDominantNormalizedEndpointCarrier k s)]
  unfold etaCriticalMirrorCompletedZetaDominantRadialRayModel
  unfold completedZetaCanonicalSlopeRayModel
  rw [← mul_sub]
  apply congrArg (fun w : ℂ => completedZetaCanonicalSlopeUnitDirection s * w)
  apply Complex.ext <;>
    simp [etaCriticalMirrorCompletedZetaDominantRadialCoordinateError,
      etaCriticalMirrorCompletedZetaDominantTransverseCoordinate,
      completedZetaCanonicalSlopeTransverseCoordinate]

/-- Pointwise approximation is exactly radial-coordinate collapse plus transverse collapse. -/
theorem etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff
    (s : ℂ) :
    Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
            etaCriticalMirrorCompletedZetaDominantRadialRayModel k s)
        atTop (nhds 0) ↔
      Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s)
          atTop (nhds 0) ∧
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s)
          atTop (nhds 0) := by
  constructor
  · intro herror
    have hcoordinate :
        Tendsto
          (fun k : ℕ =>
            (completedZetaCanonicalSlopeUnitDirection s)⁻¹ *
              (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
                etaCriticalMirrorCompletedZetaDominantRadialRayModel k s))
          atTop (nhds 0) := by
      simpa only [mul_zero] using
        (show Tendsto
            (fun _ : ℕ => (completedZetaCanonicalSlopeUnitDirection s)⁻¹)
            atTop
            (nhds (completedZetaCanonicalSlopeUnitDirection s)⁻¹) from
          tendsto_const_nhds).mul herror
    have hcomponents :
        Tendsto
          (fun k : ℕ =>
            ((etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s : ℝ) : ℂ) +
              Complex.I *
                ((etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s : ℝ) : ℂ))
          atTop (nhds 0) := by
      refine hcoordinate.congr' (Eventually.of_forall fun k => ?_)
      rw [etaCriticalMirrorCompletedZetaDominantEndpoint_sub_rayModel_eq]
      rw [← mul_assoc]
      rw [inv_mul_cancel₀ (completedZetaCanonicalSlopeUnitDirection_ne_zero s)]
      simp
    constructor
    · have hre := (Complex.continuous_re.tendsto 0).comp hcomponents
      simpa [Function.comp_def] using hre
    · have him := (Complex.continuous_im.tendsto 0).comp hcomponents
      simpa [Function.comp_def] using him
  · rintro ⟨hradial, htransverse⟩
    have hradialC :
        Tendsto
          (fun k : ℕ =>
            ((etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s : ℝ) : ℂ))
          atTop (nhds 0) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp hradial
      simpa [Function.comp_def] using h
    have htransverseC :
        Tendsto
          (fun k : ℕ =>
            ((etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s : ℝ) : ℂ))
          atTop (nhds 0) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp htransverse
      simpa [Function.comp_def] using h
    have himaginary :
        Tendsto
          (fun k : ℕ =>
            Complex.I *
              ((etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s : ℝ) : ℂ))
          atTop (nhds 0) := by
      simpa only [mul_zero] using
        (show Tendsto (fun _ : ℕ => Complex.I) atTop (nhds Complex.I) from
          tendsto_const_nhds).mul htransverseC
    have hcomponents := hradialC.add himaginary
    have hrotated :
        Tendsto
          (fun k : ℕ =>
            completedZetaCanonicalSlopeUnitDirection s *
              (((etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s : ℝ) : ℂ) +
                Complex.I *
                  ((etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s : ℝ) : ℂ)))
          atTop (nhds 0) := by
      simpa only [mul_zero] using
        (show Tendsto
            (fun _ : ℕ => completedZetaCanonicalSlopeUnitDirection s)
            atTop (nhds (completedZetaCanonicalSlopeUnitDirection s)) from
          tendsto_const_nhds).mul hcomponents
    refine hrotated.congr' (Eventually.of_forall fun k => ?_)
    exact
      (etaCriticalMirrorCompletedZetaDominantEndpoint_sub_rayModel_eq k s).symm

/-- Global radial-coordinate collapse contract. -/
def EtaCriticalMirrorCompletedZetaDominantRadialCoordinateCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorCompletedZetaDominantRadialCoordinateError k s)
      atTop (nhds 0)

/-- Global transverse-coordinate collapse contract. -/
def EtaCriticalMirrorCompletedZetaDominantTransverseCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorCompletedZetaDominantTransverseCoordinate k s)
      atTop (nhds 0)

/-- The sole ray-model approximation is equivalent to radial and transverse collapse. -/
theorem etaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation_iff_coordinates :
    EtaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation ↔
      EtaCriticalMirrorCompletedZetaDominantRadialCoordinateCollapse ∧
        EtaCriticalMirrorCompletedZetaDominantTransverseCollapse := by
  constructor
  · intro happrox
    constructor
    · intro s hs him
      exact
        (etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff s).mp
          (happrox hs him) |>.1
    · intro s hs him
      exact
        (etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff s).mp
          (happrox hs him) |>.2
  · rintro ⟨hradial, htransverse⟩
    intro s hs him
    exact
      (etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff s).mpr
        ⟨hradial hs him, htransverse hs him⟩

#print axioms completedZetaCanonicalSlope_eq_projection_add_transverse
#print axioms norm_sub_completedZetaCanonicalSlopeRealProjection
#print axioms etaCriticalMirrorCompletedZetaDominantRayApproximation_tendsto_iff
#print axioms etaCriticalMirrorCompletedZetaDominantRadialRayModelApproximation_iff_coordinates

end DkMath.RH.CFBRCProjection
