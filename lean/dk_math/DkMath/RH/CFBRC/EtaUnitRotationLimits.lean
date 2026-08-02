/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaUnitRotationBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaUnitRotationLimits"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
Under unit rotation, normalized projected eta energy is the endpoint norm-square
divided by the square of total projected mass.
-/
theorem normalizedEtaProjectedEnergy_unitRotation_eq
    (N : ℕ) (s : ℂ) :
    normalizedEtaProjectedEnergy (N + 1) s 1 =
      Complex.normSq (etaPartialEndpoint (N + 1) s) /
        projectedMassTotal
          (Finset.range (N + 1)) (etaSignedVector s) 1 ^ 2 := by
  unfold normalizedEtaProjectedEnergy
  rw [DkMath.RH.Weave.Analytic.etaAntisymmetricEnergy_eq_half_normSq_endpoint]
  norm_num [Complex.normSq_apply]

/-- Unit-rotation normalized eta energy is nonnegative. -/
theorem normalizedEtaProjectedEnergy_unitRotation_nonneg
    (N : ℕ) (s : ℂ) :
    0 ≤ normalizedEtaProjectedEnergy (N + 1) s 1 := by
  rw [normalizedEtaProjectedEnergy_unitRotation_eq]
  positivity

/--
The unit-rotation normalization cannot increase endpoint norm-square because
the total projected mass is at least one.
-/
theorem normalizedEtaProjectedEnergy_unitRotation_le_normSq
    (N : ℕ) (s : ℂ) :
    normalizedEtaProjectedEnergy (N + 1) s 1 ≤
      Complex.normSq (etaPartialEndpoint (N + 1) s) := by
  rw [normalizedEtaProjectedEnergy_unitRotation_eq]
  have hTotal :
      1 ≤ projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) 1 :=
    one_le_projectedMassTotal_eta_unitRotation N s
  have hTotalSq :
      1 ≤ projectedMassTotal
        (Finset.range (N + 1)) (etaSignedVector s) 1 ^ 2 := by
    nlinarith
  exact div_le_self (by positivity) hTotalSq

/-- Under unit rotation, normalized transverse gap is endpoint imaginary part divided by total mass. -/
theorem normalizedEtaTransverseGap_unitRotation_eq
    (N : ℕ) (s : ℂ) :
    normalizedEtaTransverseGap (N + 1) s 1 =
      (etaPartialEndpoint (N + 1) s).im /
        projectedMassTotal
          (Finset.range (N + 1)) (etaSignedVector s) 1 := by
  simp [normalizedEtaTransverseGap, transverseGap, rotatedFiniteEndpoint,
    etaPartialEndpoint]

/--
The norm of the normalized transverse gap is bounded by the norm of the finite
eta endpoint.
-/
theorem norm_normalizedEtaTransverseGap_unitRotation_le_endpoint
    (N : ℕ) (s : ℂ) :
    ‖normalizedEtaTransverseGap (N + 1) s 1‖ ≤
      ‖etaPartialEndpoint (N + 1) s‖ := by
  rw [normalizedEtaTransverseGap_unitRotation_eq]
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
    |(etaPartialEndpoint (N + 1) s).im| ≤
        ‖etaPartialEndpoint (N + 1) s‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖etaPartialEndpoint (N + 1) s‖ *
        projectedMassTotal
          (Finset.range (N + 1)) (etaSignedVector s) 1 :=
      le_mul_of_one_le_right (norm_nonneg _) hTotal

/--
Any zero limit of finite eta endpoints gives a zero limit of normalized unit-
rotation projected energy.
-/
theorem normalizedEtaProjectedEnergy_unitRotation_tendsto_zero_of_endpoint_tendsto_zero
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => normalizedEtaProjectedEnergy (N + 1) s 1)
      atTop (nhds 0) := by
  have hshift :
      Tendsto (fun N : ℕ => etaPartialEndpoint (N + 1) s)
        atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hzero
  have hnormSq :
      Tendsto
        (fun N : ℕ => Complex.normSq (etaPartialEndpoint (N + 1) s))
        atTop (nhds 0) := by
    have h := Complex.continuous_normSq.continuousAt.tendsto.comp hshift
    simpa using h
  exact squeeze_zero'
    (Eventually.of_forall fun N =>
      normalizedEtaProjectedEnergy_unitRotation_nonneg N s)
    (Eventually.of_forall fun N =>
      normalizedEtaProjectedEnergy_unitRotation_le_normSq N s)
    hnormSq

/--
Any zero limit of finite eta endpoints gives a zero limit of normalized unit-
rotation transverse displacement.
-/
theorem normalizedEtaTransverseGap_unitRotation_tendsto_zero_of_endpoint_tendsto_zero
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => normalizedEtaTransverseGap (N + 1) s 1)
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
      norm_normalizedEtaTransverseGap_unitRotation_le_endpoint N s)
    hnorm

/--
At a nonreal right-half-plane zeta zero, normalized unit-rotation projected
energy vanishes automatically.
-/
theorem normalizedEtaProjectedEnergy_unitRotation_tendsto_zero_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto
      (fun N : ℕ => normalizedEtaProjectedEnergy (N + 1) s 1)
      atTop (nhds 0) := by
  exact
    normalizedEtaProjectedEnergy_unitRotation_tendsto_zero_of_endpoint_tendsto_zero
      (DkMath.RH.Weave.Analytic.
        etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
          hre him hz)

/--
At a nonreal right-half-plane zeta zero, normalized unit-rotation transverse
displacement vanishes automatically.
-/
theorem normalizedEtaTransverseGap_unitRotation_tendsto_zero_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto
      (fun N : ℕ => normalizedEtaTransverseGap (N + 1) s 1)
      atTop (nhds 0) := by
  exact
    normalizedEtaTransverseGap_unitRotation_tendsto_zero_of_endpoint_tendsto_zero
      (DkMath.RH.Weave.Analytic.
        etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
          hre him hz)

/--
Reduced unit-rotation bridge.  Endpoint analysis automatically supplies the
normalized-energy and transverse limits, leaving only the centered-coordinate
identification as the load-bearing weave condition.
-/
structure EtaUnitCenterIdentificationCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  positive_re : ∀ {s : ℂ}, Zero s → 0 < s.re
  imaginary_ne_zero : ∀ {s : ℂ}, Zero s → s.im ≠ 0
  riemannZeta_eq_zero : ∀ {s : ℂ}, Zero s → riemannZeta s = 0
  centerOffset_tendsto_centeredSigma : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
          (Finset.range (N + 1)) (etaSignedVector s) 1)
      atTop (nhds (centeredSigma s.re))

/-- The reduced center-identification model supplies the unit-rotation bridge. -/
def EtaUnitCenterIdentificationCFBRCBridge.toEtaUnitRotationCFBRCBridge
    {Zero : ℂ → Prop}
    (bridge : EtaUnitCenterIdentificationCFBRCBridge Zero) :
    EtaUnitRotationCFBRCBridge Zero where
  d := bridge.d
  hd := bridge.hd
  phase := bridge.phase
  normalizedEnergy_tendsto_zero := fun hs =>
    normalizedEtaProjectedEnergy_unitRotation_tendsto_zero_of_riemannZeta_zero
      (bridge.positive_re hs) (bridge.imaginary_ne_zero hs)
      (bridge.riemannZeta_eq_zero hs)
  centerOffset_tendsto_centeredSigma :=
    bridge.centerOffset_tendsto_centeredSigma
  transverseGap_tendsto_zero := fun hs =>
    normalizedEtaTransverseGap_unitRotation_tendsto_zero_of_riemannZeta_zero
      (bridge.positive_re hs) (bridge.imaginary_ne_zero hs)
      (bridge.riemannZeta_eq_zero hs)

/-- Every reduced center-identification bridge supplies the standard zero-to-CFBRC bridge. -/
def EtaUnitCenterIdentificationCFBRCBridge.toZeroToCFBRCBridge
    {Zero : ℂ → Prop}
    (bridge : EtaUnitCenterIdentificationCFBRCBridge Zero) :
    ZeroToCFBRCBridge Zero :=
  bridge.toEtaUnitRotationCFBRCBridge.toZeroToCFBRCBridge

/-- Every selected zero in the reduced center-identification model lies on the critical line. -/
theorem re_eq_half_of_etaUnitCenterIdentificationCFBRCBridge
    {Zero : ℂ → Prop}
    (bridge : EtaUnitCenterIdentificationCFBRCBridge Zero)
    {s : ℂ} (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_zeroToCFBRCBridge bridge.toZeroToCFBRCBridge hs

/-- Standard-zeta specialization of the reduced center-identification bridge. -/
abbrev StandardZetaEtaUnitCenterIdentificationCFBRCBridge :=
  EtaUnitCenterIdentificationCFBRCBridge NontrivialRiemannZetaZero

/-- A standard-zeta reduced center-identification bridge proves Mathlib's formal RH. -/
theorem riemannHypothesis_of_standardZetaEtaUnitCenterIdentificationCFBRCBridge
    (bridge : StandardZetaEtaUnitCenterIdentificationCFBRCBridge) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_standardZetaToCFBRCBridge
    bridge.toZeroToCFBRCBridge

end DkMath.RH.CFBRCProjection
