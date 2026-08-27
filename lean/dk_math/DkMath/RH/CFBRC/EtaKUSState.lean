/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Coeff
import DkMath.RH.CFBRC.EtaUnitRotationLimits

#print "file: DkMath.RH.CFBRC.EtaKUSState"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.KUS
open DkMath.RH.Weave.Analytic
open DkMath.RH.Weave.Finite

/--
The structural unit of one finite eta observation.

The visible coefficient may later vanish, but the point, truncation index, and
observation rotation remain available through the KUS support.
-/
structure EtaKUSUnit where
  index : ℕ
  point : ℂ
  rotation : ℂ

/--
Blueprint retained behind a finite eta observation.

Besides the finite endpoint, it stores the critical centered coordinate and the
three projected observables together with their exact finite Pythagorean
identity.  These data remain referenceable after coefficient zeroization.
-/
structure EtaKUSBlueprint (u : EtaKUSUnit) where
  storedEndpoint : ℂ
  storedCenteredCoordinate : ℝ
  storedProjectedCenterOffset : ℝ
  storedNormalizedTransverseGap : ℝ
  storedNormalizedProjectedEnergy : ℝ
  storedEndpoint_eq :
    storedEndpoint = etaPartialEndpoint u.index u.point
  storedCenteredCoordinate_eq :
    storedCenteredCoordinate = centeredSigma u.point.re
  storedProjectedCenterOffset_eq :
    storedProjectedCenterOffset =
      normalizedProjectedCenterOffset
        (Finset.range u.index) (etaSignedVector u.point) u.rotation
  storedNormalizedTransverseGap_eq :
    storedNormalizedTransverseGap =
      normalizedEtaTransverseGap u.index u.point u.rotation
  storedNormalizedProjectedEnergy_eq :
    storedNormalizedProjectedEnergy =
      normalizedEtaProjectedEnergy u.index u.point u.rotation
  energy_decomposition :
    storedNormalizedProjectedEnergy =
      storedProjectedCenterOffset ^ 2 +
        storedNormalizedTransverseGap ^ 2

/--
Canonical KUS support for a finite eta observation with nonzero projected total
mass.
-/
noncomputable def etaKUSSupport
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    US EtaKUSUnit EtaKUSBlueprint where
  unit :=
    { index := N
      point := s
      rotation := ω }
  blueprint :=
    { storedEndpoint := etaPartialEndpoint N s
      storedCenteredCoordinate := centeredSigma s.re
      storedProjectedCenterOffset :=
        normalizedProjectedCenterOffset
          (Finset.range N) (etaSignedVector s) ω
      storedNormalizedTransverseGap :=
        normalizedEtaTransverseGap N s ω
      storedNormalizedProjectedEnergy :=
        normalizedEtaProjectedEnergy N s ω
      storedEndpoint_eq := rfl
      storedCenteredCoordinate_eq := rfl
      storedProjectedCenterOffset_eq := rfl
      storedNormalizedTransverseGap_eq := rfl
      storedNormalizedProjectedEnergy_eq := rfl
      energy_decomposition :=
        normalizedEtaProjectedEnergy_eq_centerSq_add_transverseSq
          N s ω hTotal }

/-- Finite eta endpoint carried as the visible coefficient of its KUS support. -/
noncomputable def etaKUSState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    GKUS ℂ EtaKUSUnit EtaKUSBlueprint :=
  mkGWith (etaPartialEndpoint N s) (etaKUSSupport N s ω hTotal)

/--
Structural zero obtained by erasing only the visible endpoint coefficient.
The full eta observation support is retained.
-/
noncomputable def etaKUSZeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    GKUS ℂ EtaKUSUnit EtaKUSBlueprint :=
  gZeroState (C := ℂ) (etaKUSSupport N s ω hTotal)

@[simp] theorem toCoeff_etaKUSState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    toCoeff (etaKUSState N s ω hTotal) = etaPartialEndpoint N s := rfl

@[simp] theorem toCoeff_etaKUSZeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    toCoeff (etaKUSZeroState N s ω hTotal) = 0 := rfl

@[simp] theorem extract_g_etaKUSZeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    extract_g (etaKUSZeroState N s ω hTotal) =
      etaKUSSupport N s ω hTotal := by
  simp [etaKUSZeroState]

/-- The centered coordinate remains directly readable after zeroization. -/
@[simp] theorem etaKUSZeroState_storedCenteredCoordinate
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    (etaKUSZeroState N s ω hTotal).blueprint.storedCenteredCoordinate =
      centeredSigma s.re := rfl

/-- The original finite endpoint remains recorded in the zero-state blueprint. -/
@[simp] theorem etaKUSZeroState_storedEndpoint
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    (etaKUSZeroState N s ω hTotal).blueprint.storedEndpoint =
      etaPartialEndpoint N s := rfl

/-- The finite projected-energy decomposition survives coefficient zeroization. -/
theorem etaKUSZeroState_energy_decomposition
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    (etaKUSZeroState N s ω hTotal).blueprint.storedNormalizedProjectedEnergy =
      (etaKUSZeroState N s ω hTotal).blueprint.storedProjectedCenterOffset ^ 2 +
        (etaKUSZeroState N s ω hTotal).blueprint.storedNormalizedTransverseGap ^ 2 :=
  (etaKUSZeroState N s ω hTotal).blueprint.energy_decomposition

/-- Unit-rotation support, available at every nonempty finite eta stage. -/
noncomputable def etaUnitKUSSupport (N : ℕ) (s : ℂ) :
    US EtaKUSUnit EtaKUSBlueprint :=
  etaKUSSupport (N + 1) s 1
    (projectedMassTotal_eta_unitRotation_ne_zero N s)

/-- Unit-rotation eta state with the finite endpoint as visible coefficient. -/
noncomputable def etaUnitKUSState (N : ℕ) (s : ℂ) :
    GKUS ℂ EtaKUSUnit EtaKUSBlueprint :=
  mkGWith (etaPartialEndpoint (N + 1) s) (etaUnitKUSSupport N s)

/-- Unit-rotation structural zero retaining the entire finite observation. -/
noncomputable def etaUnitKUSZeroState (N : ℕ) (s : ℂ) :
    GKUS ℂ EtaKUSUnit EtaKUSBlueprint :=
  gZeroState (C := ℂ) (etaUnitKUSSupport N s)

@[simp] theorem toCoeff_etaUnitKUSZeroState (N : ℕ) (s : ℂ) :
    toCoeff (etaUnitKUSZeroState N s) = 0 := rfl

@[simp] theorem extract_g_etaUnitKUSZeroState (N : ℕ) (s : ℂ) :
    extract_g (etaUnitKUSZeroState N s) = etaUnitKUSSupport N s := by
  simp [etaUnitKUSZeroState]

@[simp] theorem etaUnitKUSZeroState_storedCenteredCoordinate
    (N : ℕ) (s : ℂ) :
    (etaUnitKUSZeroState N s).blueprint.storedCenteredCoordinate =
      centeredSigma s.re := rfl

/--
Equality of structural eta zero states forces equality of the retained
observation coordinates.  Thus coefficient zero does not identify distinct
truncation stages, complex points, or rotations.
-/
theorem etaKUSZeroState_coordinates_eq_of_eq
    {N₁ N₂ : ℕ} {s₁ s₂ ω₁ ω₂ : ℂ}
    {hTotal₁ :
      projectedMassTotal (Finset.range N₁) (etaSignedVector s₁) ω₁ ≠ 0}
    {hTotal₂ :
      projectedMassTotal (Finset.range N₂) (etaSignedVector s₂) ω₂ ≠ 0}
    (hzero :
      etaKUSZeroState N₁ s₁ ω₁ hTotal₁ =
        etaKUSZeroState N₂ s₂ ω₂ hTotal₂) :
    N₁ = N₂ ∧ s₁ = s₂ ∧ ω₁ = ω₂ := by
  have hunit := congrArg
    (fun x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint => x.unit) hzero
  constructor
  · simpa [etaKUSZeroState, etaKUSSupport] using
      congrArg EtaKUSUnit.index hunit
  · constructor
    · simpa [etaKUSZeroState, etaKUSSupport] using
        congrArg EtaKUSUnit.point hunit
    · simpa [etaKUSZeroState, etaKUSSupport] using
        congrArg EtaKUSUnit.rotation hunit

end DkMath.RH.CFBRCProjection
