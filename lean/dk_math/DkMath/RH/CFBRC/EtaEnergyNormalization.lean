/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.FiniteMassNormalization
import DkMath.RH.Weave.Analytic.EtaEnergyLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaEnergyNormalization"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Finite
open DkMath.RH.Weave.Analytic

/--
The normalized projected center offset, multiplied back by total projected
mass, is exactly the real component of the rotated finite endpoint.
-/
theorem normalizedProjectedCenterOffset_mul_projectedMassTotal
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedProjectedCenterOffset S v ω *
        projectedMassTotal S v ω =
      (rotatedFiniteEndpoint S v ω).re := by
  calc
    normalizedProjectedCenterOffset S v ω *
          projectedMassTotal S v ω =
        (positiveProjectedMass S v ω /
            projectedMassTotal S v ω -
          negativeProjectedMass S v ω /
            projectedMassTotal S v ω) *
          projectedMassTotal S v ω := by
            rfl
    _ = positiveProjectedMass S v ω -
          negativeProjectedMass S v ω := by
            field_simp [hTotal]
    _ = (rotatedFiniteEndpoint S v ω).re :=
      (rotatedFiniteEndpoint_re_eq_mass_sub S v ω).symm

/--
Denominator-free Pythagorean identity for the normalized projected center.
The longitudinal center contribution plus the transverse residual reconstructs
the squared norm of the rotated endpoint.
-/
theorem normalizedProjectedCenter_energy_decomposition
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedProjectedCenterOffset S v ω ^ 2 *
          projectedMassTotal S v ω ^ 2 +
        transverseGap S v ω ^ 2 =
      Complex.normSq (rotatedFiniteEndpoint S v ω) := by
  have hreal :=
    normalizedProjectedCenterOffset_mul_projectedMassTotal
      S v ω hTotal
  have hrealSq := congrArg (fun x : ℝ => x ^ 2) hreal
  simp only [Complex.normSq_apply]
  unfold transverseGap
  nlinarith

/--
The same denominator-free identity expressed before the common rotation: the
rotated endpoint energy is the rotation norm-square times the original finite
endpoint energy.
-/
theorem normalizedProjectedCenter_energy_decomposition_unrotated
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedProjectedCenterOffset S v ω ^ 2 *
          projectedMassTotal S v ω ^ 2 +
        transverseGap S v ω ^ 2 =
      Complex.normSq ω * Complex.normSq (finiteEndpoint S v) := by
  rw [normalizedProjectedCenter_energy_decomposition S v ω hTotal]
  simp [rotatedFiniteEndpoint, Complex.normSq_mul]

/--
Finite eta energy conservation in projected coordinates.  The left side is
the center-offset contribution plus the transverse contribution; the right
side is exactly the antisymmetric eta energy with its rotation factor restored.
-/
theorem etaProjectedCenter_energy_decomposition
    (N : ℕ) (s : ℂ) (ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    normalizedProjectedCenterOffset
          (Finset.range N) (etaSignedVector s) ω ^ 2 *
        projectedMassTotal
          (Finset.range N) (etaSignedVector s) ω ^ 2 +
        transverseGap (Finset.range N) (etaSignedVector s) ω ^ 2 =
      2 * Complex.normSq ω * etaAntisymmetricEnergy N s := by
  rw [normalizedProjectedCenter_energy_decomposition_unrotated
    (Finset.range N) (etaSignedVector s) ω hTotal]
  rw [etaAntisymmetricEnergy_eq_half_normSq_endpoint]
  unfold etaPartialEndpoint
  ring

/-- Projected antisymmetric eta energy normalized by total projected mass. -/
noncomputable def normalizedEtaProjectedEnergy
    (N : ℕ) (s : ℂ) (ω : ℂ) : ℝ :=
  2 * Complex.normSq ω * etaAntisymmetricEnergy N s /
    projectedMassTotal (Finset.range N) (etaSignedVector s) ω ^ 2

/-- Transverse eta residual normalized by total projected mass. -/
noncomputable def normalizedEtaTransverseGap
    (N : ℕ) (s : ℂ) (ω : ℂ) : ℝ :=
  transverseGap (Finset.range N) (etaSignedVector s) ω /
    projectedMassTotal (Finset.range N) (etaSignedVector s) ω

/--
The normalized eta energy splits exactly into centered projected displacement
squared plus normalized transverse displacement squared.
-/
theorem normalizedEtaProjectedEnergy_eq_centerSq_add_transverseSq
    (N : ℕ) (s : ℂ) (ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    normalizedEtaProjectedEnergy N s ω =
      normalizedProjectedCenterOffset
          (Finset.range N) (etaSignedVector s) ω ^ 2 +
        normalizedEtaTransverseGap N s ω ^ 2 := by
  have henergy := etaProjectedCenter_energy_decomposition N s ω hTotal
  unfold normalizedEtaProjectedEnergy normalizedEtaTransverseGap
  field_simp [hTotal]
  nlinarith

end DkMath.RH.CFBRCProjection
