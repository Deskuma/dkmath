/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSLimit
import DkMath.RH.CFBRC.EtaProjectedEnergyBridge

#print "file: DkMath.RH.CFBRC.EtaKUSProjectedCenterDecoder"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.KUS
open DkMath.RH.Weave.Analytic
open DkMath.RH.Weave.Finite

/--
Reconstruct the normalized projected center directly from the structural KUS
unit.  This decoder uses only the retained truncation index, observation point,
and rotation.  In particular, it does not read `storedCenteredCoordinate` from
the blueprint.
-/
noncomputable def etaKUSProjectedCenterDecoder
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) : ℝ :=
  normalizedProjectedCenterOffset
    (Finset.range x.unit.index)
    (etaSignedVector x.unit.point)
    x.unit.rotation

/--
The independently reconstructed center agrees with the projected-center value
recorded in the blueprint.  The centered sigma field is not used.
-/
theorem etaKUSProjectedCenterDecoder_eq_storedProjectedCenterOffset
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) :
    etaKUSProjectedCenterDecoder x =
      x.blueprint.storedProjectedCenterOffset := by
  exact x.blueprint.storedProjectedCenterOffset_eq.symm

/-- The decoder depends only on the structural unit, not on the coefficient. -/
theorem etaKUSProjectedCenterDecoder_eq_of_unit_eq
    {x y : GKUS ℂ EtaKUSUnit EtaKUSBlueprint}
    (hunit : x.unit = y.unit) :
    etaKUSProjectedCenterDecoder x =
      etaKUSProjectedCenterDecoder y := by
  simp [etaKUSProjectedCenterDecoder, hunit]

@[simp] theorem etaKUSProjectedCenterDecoder_etaKUSState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    etaKUSProjectedCenterDecoder (etaKUSState N s ω hTotal) =
      normalizedProjectedCenterOffset
        (Finset.range N) (etaSignedVector s) ω := rfl

@[simp] theorem etaKUSProjectedCenterDecoder_etaKUSZeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    etaKUSProjectedCenterDecoder (etaKUSZeroState N s ω hTotal) =
      normalizedProjectedCenterOffset
        (Finset.range N) (etaSignedVector s) ω := rfl

/-- Coefficient zeroization leaves the structural projected-center reading unchanged. -/
theorem etaKUSProjectedCenterDecoder_state_eq_zeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    etaKUSProjectedCenterDecoder (etaKUSState N s ω hTotal) =
      etaKUSProjectedCenterDecoder (etaKUSZeroState N s ω hTotal) := by
  rfl

/--
A phase-dependent eta KUS trace.  The support at stage `N` retains the genuine
finite eta observation of length `N + 1`.
-/
noncomputable def etaPhaseKUSTrace
    (rotation : ℕ → ℂ → ℂ) (s : ℂ)
    (hTotal : ∀ N : ℕ,
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0) :
    ℕ → GKUS ℂ EtaKUSUnit EtaKUSBlueprint :=
  fun N =>
    etaKUSState (N + 1) s (rotation N s) (hTotal N)

@[simp] theorem etaPhaseKUSTrace_point
    (rotation : ℕ → ℂ → ℂ) (s : ℂ)
    (hTotal : ∀ N : ℕ,
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0)
    (N : ℕ) :
    (etaPhaseKUSTrace rotation s hTotal N).unit.point = s := rfl

@[simp] theorem etaPhaseKUSTrace_index
    (rotation : ℕ → ℂ → ℂ) (s : ℂ)
    (hTotal : ∀ N : ℕ,
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0)
    (N : ℕ) :
    (etaPhaseKUSTrace rotation s hTotal N).unit.index = N + 1 := rfl

@[simp] theorem etaPhaseKUSTrace_rotation
    (rotation : ℕ → ℂ → ℂ) (s : ℂ)
    (hTotal : ∀ N : ℕ,
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0)
    (N : ℕ) :
    (etaPhaseKUSTrace rotation s hTotal N).unit.rotation =
      rotation N s := rfl

@[simp] theorem etaKUSProjectedCenterDecoder_etaPhaseKUSTrace
    (rotation : ℕ → ℂ → ℂ) (s : ℂ)
    (hTotal : ∀ N : ℕ,
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0)
    (N : ℕ) :
    etaKUSProjectedCenterDecoder
        (etaPhaseKUSTrace rotation s hTotal N) =
      normalizedProjectedCenterOffset
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) := rfl

/--
The remaining non-circular center obligation, stated on the KUS decoder trace.
A realization must derive this limit from retained eta/phase structure rather
than from the blueprint's stored centered coordinate.
-/
structure EtaKUSProjectedCenterDecoderBridge (Zero : ℂ → Prop) where
  rotation : ℕ → ℂ → ℂ
  projectedMassTotal_ne_zero : ∀ {s : ℂ}, Zero s → ∀ N : ℕ,
    projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0
  decoder_tendsto_centeredSigma : ∀ {s : ℂ}, (hs : Zero s) →
    Tendsto
      (fun N : ℕ =>
        etaKUSProjectedCenterDecoder
          (etaPhaseKUSTrace rotation s
            (projectedMassTotal_ne_zero hs) N))
      atTop (nhds (centeredSigma s.re))

/-- The decoder limit supplies the center-offset field of the projected bridge. -/
theorem EtaKUSProjectedCenterDecoderBridge.centerOffset_tendsto_centeredSigma
    {Zero : ℂ → Prop} (bridge : EtaKUSProjectedCenterDecoderBridge Zero)
    {s : ℂ} (hs : Zero s) :
    Tendsto
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
          (Finset.range (N + 1)) (etaSignedVector s)
            (bridge.rotation N s))
      atTop (nhds (centeredSigma s.re)) := by
  simpa using bridge.decoder_tendsto_centeredSigma hs

/--
Assemble the existing projected-energy bridge once the decoder, energy, and
transverse limits have been proved independently.
-/
noncomputable def
    EtaKUSProjectedCenterDecoderBridge.toEtaProjectedEnergyCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaKUSProjectedCenterDecoderBridge Zero)
    (d : ℕ) (hd : 0 < d) (phase : ℂ → ℝ)
    (normalizedEnergy_tendsto_zero : ∀ {s : ℂ}, Zero s →
      Tendsto
        (fun N : ℕ =>
          normalizedEtaProjectedEnergy
            (N + 1) s (bridge.rotation N s))
        atTop (nhds 0))
    (transverseGap_tendsto_zero : ∀ {s : ℂ}, Zero s →
      Tendsto
        (fun N : ℕ =>
          normalizedEtaTransverseGap
            (N + 1) s (bridge.rotation N s))
        atTop (nhds 0)) :
    EtaProjectedEnergyCFBRCBridge Zero where
  d := d
  hd := hd
  phase := phase
  rotation := bridge.rotation
  projectedMassTotal_ne_zero := bridge.projectedMassTotal_ne_zero
  normalizedEnergy_tendsto_zero := normalizedEnergy_tendsto_zero
  centerOffset_tendsto_centeredSigma :=
    bridge.centerOffset_tendsto_centeredSigma
  transverseGap_tendsto_zero := transverseGap_tendsto_zero

end DkMath.RH.CFBRCProjection
