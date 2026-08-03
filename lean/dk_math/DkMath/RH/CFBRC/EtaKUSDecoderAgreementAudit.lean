/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSMirrorAmplitudeBridge
import DkMath.RH.CFBRC.EtaUnitRotationLimits
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaKUSDecoderAgreementAudit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic
open DkMath.RH.Weave.Finite

/--
Under unit rotation, the normalized projected center is the real part of the
finite eta endpoint divided by total projected mass.
-/
theorem normalizedProjectedCenterOffset_unitRotation_eq
    (N : ℕ) (s : ℂ) :
    normalizedProjectedCenterOffset
        (Finset.range (N + 1)) (etaSignedVector s) 1 =
      (etaPartialEndpoint (N + 1) s).re /
        projectedMassTotal
          (Finset.range (N + 1)) (etaSignedVector s) 1 := by
  have hTotal :
      projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) 1 ≠ 0 :=
    projectedMassTotal_eta_unitRotation_ne_zero N s
  apply (eq_div_iff hTotal).2
  simpa [rotatedFiniteEndpoint, etaPartialEndpoint] using
    normalizedProjectedCenterOffset_mul_projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) 1 hTotal

/--
The norm of the unit-rotation projected center is bounded by the norm of the
finite eta endpoint.
-/
theorem norm_normalizedProjectedCenterOffset_unitRotation_le_endpoint
    (N : ℕ) (s : ℂ) :
    ‖normalizedProjectedCenterOffset
        (Finset.range (N + 1)) (etaSignedVector s) 1‖ ≤
      ‖etaPartialEndpoint (N + 1) s‖ := by
  rw [normalizedProjectedCenterOffset_unitRotation_eq]
  have hTotal :
      1 ≤ projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) 1 :=
    one_le_projectedMassTotal_eta_unitRotation N s
  have hTotalPos :
      0 < projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) 1 :=
    zero_lt_one.trans_le hTotal
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hTotalPos]
  apply (div_le_iff₀ hTotalPos).2
  calc
    |(etaPartialEndpoint (N + 1) s).re| ≤
        ‖etaPartialEndpoint (N + 1) s‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖etaPartialEndpoint (N + 1) s‖ *
        projectedMassTotal
          (Finset.range (N + 1)) (etaSignedVector s) 1 :=
      le_mul_of_one_le_right (norm_nonneg _) hTotal

/-- Endpoint convergence to zero forces the unit projected-center decoder to zero. -/
theorem normalizedProjectedCenterOffset_unitRotation_tendsto_zero_of_endpoint_tendsto_zero
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
          (Finset.range (N + 1)) (etaSignedVector s) 1)
      atTop (nhds 0) := by
  have hshift :
      Tendsto (fun N : ℕ => etaPartialEndpoint (N + 1) s)
        atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hzero
  have hnorm :
      Tendsto (fun N : ℕ => ‖etaPartialEndpoint (N + 1) s‖)
        atTop (nhds 0) := by
    simpa using hshift.norm
  exact squeeze_zero_norm'
    (Eventually.of_forall fun N =>
      norm_normalizedProjectedCenterOffset_unitRotation_le_endpoint N s)
    hnorm

/-- At every nonreal right-half-plane zeta zero, the unit center tends to zero. -/
theorem normalizedProjectedCenterOffset_unitRotation_tendsto_zero_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
          (Finset.range (N + 1)) (etaSignedVector s) 1)
      atTop (nhds 0) := by
  exact
    normalizedProjectedCenterOffset_unitRotation_tendsto_zero_of_endpoint_tendsto_zero
      (etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
        hre him hz)

/-- The KUS unit trace carries exactly the unit-rotation projected-center sequence. -/
theorem etaKUSProjectedCenterDecoder_etaUnitKUSTrace
    (N : ℕ) (s : ℂ) :
    etaKUSProjectedCenterDecoder (etaUnitKUSTrace s N) =
      normalizedProjectedCenterOffset
        (Finset.range (N + 1)) (etaSignedVector s) 1 := rfl

/-- At a standard zeta zero, the KUS unit projected decoder tends to zero. -/
theorem etaKUSProjectedCenterDecoder_etaUnitKUSTrace_tendsto_zero_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto
      (fun N : ℕ =>
        etaKUSProjectedCenterDecoder (etaUnitKUSTrace s N))
      atTop (nhds 0) := by
  simpa only [etaKUSProjectedCenterDecoder_etaUnitKUSTrace] using
    normalizedProjectedCenterOffset_unitRotation_tendsto_zero_of_riemannZeta_zero
      hre him hz

/--
Load-bearing audit: at a zeta zero, agreement between the unit projected
decoder and the independent mirror-amplitude decoder is equivalent to the
vanishing of the centered coordinate.
-/
theorem etaUnitProjectedDecoder_tendsto_mirrorAmplitude_iff_centeredSigma_eq_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto
        (fun N : ℕ =>
          etaKUSProjectedCenterDecoder (etaUnitKUSTrace s N))
        atTop (nhds (etaMirrorAmplitudeDecoder s)) ↔
      centeredSigma s.re = 0 := by
  have hzero :=
    etaKUSProjectedCenterDecoder_etaUnitKUSTrace_tendsto_zero_of_riemannZeta_zero
      hre him hz
  constructor
  · intro hagree
    have htarget : (0 : ℝ) = etaMirrorAmplitudeDecoder s :=
      tendsto_nhds_unique hzero hagree
    rw [etaMirrorAmplitudeDecoder_eq_centeredSigma] at htarget
    exact htarget.symm
  · intro hcenter
    rw [etaMirrorAmplitudeDecoder_eq_centeredSigma, hcenter]
    exact hzero

/-- The same audit expressed directly as membership on the critical line. -/
theorem etaUnitProjectedDecoder_tendsto_mirrorAmplitude_iff_re_eq_half
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto
        (fun N : ℕ =>
          etaKUSProjectedCenterDecoder (etaUnitKUSTrace s N))
        atTop (nhds (etaMirrorAmplitudeDecoder s)) ↔
      s.re = (1 : ℝ) / 2 := by
  rw [etaUnitProjectedDecoder_tendsto_mirrorAmplitude_iff_centeredSigma_eq_zero
    hre him hz]
  exact centeredSigma_eq_zero_iff s.re

end DkMath.RH.CFBRCProjection
