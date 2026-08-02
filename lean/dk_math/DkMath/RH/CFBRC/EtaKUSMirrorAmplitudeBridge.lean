/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSProjectedCenterDecoder
import DkMath.RH.CFBRC.EtaMirrorAmplitudeDecoder

#print "file: DkMath.RH.CFBRC.EtaKUSMirrorAmplitudeBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.KUS
open DkMath.RH.Weave.Finite

/--
Read the mirror-amplitude coordinate from the complex observation point retained
in a KUS structural unit.  The visible coefficient and all blueprint fields are
irrelevant to this decoder.
-/
noncomputable def etaKUSMirrorAmplitudeDecoder
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) : ℝ :=
  etaMirrorAmplitudeDecoder x.unit.point

/-- Every KUS mirror-amplitude reading is the centered real coordinate of its point. -/
theorem etaKUSMirrorAmplitudeDecoder_eq_centeredSigma
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) :
    etaKUSMirrorAmplitudeDecoder x =
      centeredSigma x.unit.point.re := by
  exact etaMirrorAmplitudeDecoder_eq_centeredSigma x.unit.point

@[simp] theorem etaKUSMirrorAmplitudeDecoder_etaKUSState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    etaKUSMirrorAmplitudeDecoder (etaKUSState N s ω hTotal) =
      centeredSigma s.re := by
  have hpoint : (etaKUSState N s ω hTotal).unit.point = s := rfl
  rw [etaKUSMirrorAmplitudeDecoder, hpoint]
  exact etaMirrorAmplitudeDecoder_eq_centeredSigma s

@[simp] theorem etaKUSMirrorAmplitudeDecoder_etaKUSZeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    etaKUSMirrorAmplitudeDecoder (etaKUSZeroState N s ω hTotal) =
      centeredSigma s.re := by
  have hpoint : (etaKUSZeroState N s ω hTotal).unit.point = s := rfl
  rw [etaKUSMirrorAmplitudeDecoder, hpoint]
  exact etaMirrorAmplitudeDecoder_eq_centeredSigma s

/-- Coefficient zeroization preserves the mirror-amplitude decoder exactly. -/
theorem etaKUSMirrorAmplitudeDecoder_state_eq_zeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    etaKUSMirrorAmplitudeDecoder (etaKUSState N s ω hTotal) =
      etaKUSMirrorAmplitudeDecoder (etaKUSZeroState N s ω hTotal) := by
  rfl

@[simp] theorem etaKUSMirrorAmplitudeDecoder_etaPhaseKUSTrace
    (rotation : ℕ → ℂ → ℂ) (s : ℂ)
    (hTotal : ∀ N : ℕ,
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0)
    (N : ℕ) :
    etaKUSMirrorAmplitudeDecoder
        (etaPhaseKUSTrace rotation s hTotal N) =
      centeredSigma s.re := by
  simpa [etaKUSMirrorAmplitudeDecoder] using
    etaMirrorAmplitudeDecoder_eq_centeredSigma s

/--
Structural form of the remaining center-limit obligation.

Instead of naming `centeredSigma s.re` as the target directly, a realization
must show that the projected finite decoder converges to the independently
reconstructed mirror-amplitude decoder.
-/
structure EtaKUSDecoderAgreementBridge (Zero : ℂ → Prop) where
  rotation : ℕ → ℂ → ℂ
  projectedMassTotal_ne_zero : ∀ {s : ℂ}, Zero s → ∀ N : ℕ,
    projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) (rotation N s) ≠ 0
  projectedDecoder_tendsto_mirrorAmplitude : ∀ {s : ℂ}, (hs : Zero s) →
    Tendsto
      (fun N : ℕ =>
        etaKUSProjectedCenterDecoder
          (etaPhaseKUSTrace rotation s
            (projectedMassTotal_ne_zero hs) N))
      atTop (nhds (etaMirrorAmplitudeDecoder s))

/-- Decoder agreement supplies the previous centered-coordinate decoder bridge. -/
noncomputable def
    EtaKUSDecoderAgreementBridge.toEtaKUSProjectedCenterDecoderBridge
    {Zero : ℂ → Prop} (bridge : EtaKUSDecoderAgreementBridge Zero) :
    EtaKUSProjectedCenterDecoderBridge Zero where
  rotation := bridge.rotation
  projectedMassTotal_ne_zero := bridge.projectedMassTotal_ne_zero
  decoder_tendsto_centeredSigma := fun {s} hs => by
    simpa only [etaMirrorAmplitudeDecoder_eq_centeredSigma] using
      bridge.projectedDecoder_tendsto_mirrorAmplitude hs

end DkMath.RH.CFBRCProjection
