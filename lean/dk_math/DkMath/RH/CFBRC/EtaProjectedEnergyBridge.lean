/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaEnergyBridge
import DkMath.RH.CFBRC.EtaEnergyNormalization
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaProjectedEnergyBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
Concrete projected-energy realization of a selected complex-zero predicate.

For each selected point, the realization chooses finite observation rotations.
The normalized eta energy must vanish, the normalized projected center must
converge to `s.re - 1/2`, and the normalized transverse gap must vanish.
The exact finite energy decomposition then forces the centered coordinate to
vanish.

The finite support uses `N + 1`, avoiding the empty endpoint at `N = 0`.
-/
structure EtaProjectedEnergyCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  rotation : ℕ → ℂ → ℂ
  projectedMassTotal_ne_zero : ∀ {s : ℂ}, Zero s → ∀ N : ℕ,
    projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0
  normalizedEnergy_tendsto_zero : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ =>
        normalizedEtaProjectedEnergy (N + 1) s (rotation N s))
      atTop (nhds 0)
  centerOffset_tendsto_centeredSigma : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
          (Finset.range (N + 1)) (etaSignedVector s) (rotation N s))
      atTop (nhds (centeredSigma s.re))
  transverseGap_tendsto_zero : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ =>
        normalizedEtaTransverseGap (N + 1) s (rotation N s))
      atTop (nhds 0)

/--
The exact finite decomposition lifts to the centered-square limit.
-/
theorem EtaProjectedEnergyCFBRCBridge.normalizedEnergy_tendsto_centeredSq
    {Zero : ℂ → Prop} (bridge : EtaProjectedEnergyCFBRCBridge Zero)
    {s : ℂ} (hs : Zero s) :
    Tendsto
      (fun N : ℕ =>
        normalizedEtaProjectedEnergy (N + 1) s (bridge.rotation N s))
      atTop (nhds (centeredSigma s.re ^ 2)) := by
  have hcenter := bridge.centerOffset_tendsto_centeredSigma hs
  have hgap := bridge.transverseGap_tendsto_zero hs
  have hcenterSq :
      Tendsto
        (fun N : ℕ =>
          normalizedProjectedCenterOffset
              (Finset.range (N + 1)) (etaSignedVector s)
                (bridge.rotation N s) ^ 2)
        atTop (nhds (centeredSigma s.re ^ 2)) := by
    simpa [pow_two] using hcenter.mul hcenter
  have hgapSq :
      Tendsto
        (fun N : ℕ =>
          normalizedEtaTransverseGap
              (N + 1) s (bridge.rotation N s) ^ 2)
        atTop (nhds (0 : ℝ)) := by
    simpa [pow_two] using hgap.mul hgap
  have hsum := hcenterSq.add hgapSq
  have hfun :
      (fun N : ℕ =>
        normalizedEtaProjectedEnergy (N + 1) s (bridge.rotation N s)) =
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
              (Finset.range (N + 1)) (etaSignedVector s)
                (bridge.rotation N s) ^ 2 +
          normalizedEtaTransverseGap
              (N + 1) s (bridge.rotation N s) ^ 2) := by
    funext N
    exact normalizedEtaProjectedEnergy_eq_centerSq_add_transverseSq
      (N + 1) s (bridge.rotation N s)
      (bridge.projectedMassTotal_ne_zero hs N)
  rw [hfun]
  simpa using hsum

/-- The projected-energy realization forces the centered coordinate to vanish. -/
theorem EtaProjectedEnergyCFBRCBridge.centeredSigma_eq_zero
    {Zero : ℂ → Prop} (bridge : EtaProjectedEnergyCFBRCBridge Zero)
    {s : ℂ} (hs : Zero s) :
    centeredSigma s.re = 0 := by
  have hsq : (0 : ℝ) = centeredSigma s.re ^ 2 :=
    tendsto_nhds_unique
      (bridge.normalizedEnergy_tendsto_zero hs)
      (bridge.normalizedEnergy_tendsto_centeredSq hs)
  nlinarith [sq_nonneg (centeredSigma s.re)]

/-- Every projected-energy realization supplies the standard zero-to-CFBRC bridge. -/
def EtaProjectedEnergyCFBRCBridge.toZeroToCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaProjectedEnergyCFBRCBridge Zero) :
    ZeroToCFBRCBridge Zero where
  d := bridge.d
  hd := bridge.hd
  phase := bridge.phase
  map_zero := fun hs => by
    apply
      (offCriticalCFBRC_eq_zero_iff_re_eq_half
        bridge.hd _ (bridge.phase _)).2
    exact (centeredSigma_eq_zero_iff _).mp
      (bridge.centeredSigma_eq_zero hs)

/-- A selected zero in the projected-energy realization lies on the critical line. -/
theorem re_eq_half_of_etaProjectedEnergyCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaProjectedEnergyCFBRCBridge Zero)
    {s : ℂ} (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_zeroToCFBRCBridge bridge.toZeroToCFBRCBridge hs

/-- Standard-zeta specialization of the projected eta-energy realization. -/
abbrev StandardZetaEtaProjectedEnergyCFBRCBridge :=
  EtaProjectedEnergyCFBRCBridge NontrivialRiemannZetaZero

/-- A standard-zeta projected-energy realization proves Mathlib's formal RH. -/
theorem riemannHypothesis_of_standardZetaEtaProjectedEnergyCFBRCBridge
    (bridge : StandardZetaEtaProjectedEnergyCFBRCBridge) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_standardZetaToCFBRCBridge
    bridge.toZeroToCFBRCBridge

end DkMath.RH.CFBRCProjection
