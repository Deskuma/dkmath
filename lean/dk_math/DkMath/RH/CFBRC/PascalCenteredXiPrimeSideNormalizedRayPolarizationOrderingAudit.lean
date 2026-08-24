/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideGeometricRaySignedNumeratorAudit
import Mathlib.Tactic

/-!
# CS17: normalized finite-ray polarization and aggregate ordering audit

This module polarizes the finite CS16 signed numerator into two normalized
complex norm-square densities.  It records the exact finite ray, interval,
and prime-weighted aggregate identities.  No ordering provider, infinite
exchange, endpoint sign theorem, or RH conclusion is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open scoped ComplexConjugate Interval Topology

/-! ## CS17-A: the two source factors -/

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
        (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1))

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector
    (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) (t : ℝ) : ℂ :=
  1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t

theorem pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_eq_re_endpoint_mul_conj
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t =
      Complex.re
        (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t *
          conj (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) := by
  rfl

/-! ## CS17-B: ordinary complex polarization -/

theorem complex_four_mul_re_mul_conj_eq_normSq_add_sub_normSq_sub
    (A B : ℂ) :
    4 * Complex.re (A * conj B) =
      Complex.normSq (A + B) - Complex.normSq (A - B) := by
  simp [Complex.normSq_apply]
  ring

theorem pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_polarization
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    4 * pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t =
      Complex.normSq
          (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
            pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) -
        Complex.normSq
          (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
            pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) := by
  rw [pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_eq_re_endpoint_mul_conj]
  exact complex_four_mul_re_mul_conj_eq_normSq_add_sub_normSq_sub _ _

theorem pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_nonneg_iff_normSq_order
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    0 ≤ pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t ↔
      Complex.normSq
          (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
            pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) ≤
        Complex.normSq
          (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
            pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) := by
  have hpol := pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_polarization
    ε W X p t
  constructor <;> intro h <;> linarith

theorem pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_nonpos_iff_normSq_order
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t ≤ 0 ↔
      Complex.normSq
          (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
            pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) ≤
        Complex.normSq
          (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
            pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) := by
  have hpol := pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_polarization
    ε W X p t
  constructor <;> intro h <;> linarith

/-! ## CS17-C: normalized plus/minus densities -/

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq
      (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) /
    Complex.normSq (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq
      (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) /
    Complex.normSq (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)

theorem pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_normSq_pos
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    0 < Complex.normSq
      (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) := by
  exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_normSq_pos W hp t

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    0 ≤ pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
  exact div_nonneg (Complex.normSq_nonneg _)
    (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_normSq_pos
      W hp t).le

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    0 ≤ pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
  exact div_nonneg (Complex.normSq_nonneg _)
    (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_normSq_pos
      W hp t).le

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_eq_normalized_density_difference
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    4 * (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re =
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t -
        pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t := by
  rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_eq_signedNumerator_div_normSq
    W hp t]
  have hpol := pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_polarization
    ε W X p t
  have hpol' :
      4 * pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t =
        Complex.normSq
            (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
              (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)) -
          Complex.normSq
            (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
              (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)) := by
    simpa [pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector] using hpol
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
    pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector
  rw [← mul_div_assoc, ← sub_div, hpol']

/-! ## CS17-D: finite continuity and ray energies -/

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t /
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t := by
  let q := pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t
  let h := pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t)
  let m := pascalCenteredXiPrimeSidePrimePowerRayLength X p
  have hq : 1 - q ≠ 0 := by
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  apply (eq_div_iff hq).2
  calc
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t * (1 - q) =
        (1 - q) * pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t := by
          ring
    _ = h * (q - q ^ (m + 1)) := by
      exact pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_weighted_compression
        W hp t

private theorem continuous_pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    Continuous
      (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p) := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    change Continuous (fun t : ℝ =>
      (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hnode : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSideModePhaseNode W t) := by
    unfold pascalCenteredXiPrimeSideModePhaseNode
    change Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t - criticalLineCenter)
    exact hpath.sub continuous_const
  have hweight : Continuous (fun t : ℝ =>
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalCenteredXiPrimeSideModePhaseNode W t)) :=
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε).continuous.comp hnode
  have hq : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) := by
    unfold pascalCenteredXiPrimeSidePrimeRatioAtRightEdge
      pascalCenteredXiPrimeSidePrimeRatio
    let : NeZero ((p : ℕ) : ℂ) :=
      ⟨by exact_mod_cast hp.ne_zero⟩
    exact (continuous_const_cpow ((p : ℕ) : ℂ)).comp
      (continuous_neg.comp hpath)
  have hqpow : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
        (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1)) :=
    hq.pow _
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
  exact hweight.mul (hq.sub hqpow)

private theorem continuous_pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) :
    Continuous (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p) := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    change Continuous (fun t : ℝ =>
      (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hq : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) := by
    unfold pascalCenteredXiPrimeSidePrimeRatioAtRightEdge
      pascalCenteredXiPrimeSidePrimeRatio
    let : NeZero ((p : ℕ) : ℂ) :=
      ⟨by exact_mod_cast hp.ne_zero⟩
    exact (continuous_const_cpow ((p : ℕ) : ℂ)).comp
      (continuous_neg.comp hpath)
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector
  exact continuous_const.sub hq

private theorem continuous_pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    Continuous (pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p) := by
  have hA := continuous_pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    hε W (X := X) hp
  have hB := continuous_pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W hp
  have hnum : Continuous (fun t : ℝ =>
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
          pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) :=
    Complex.continuous_normSq.comp (hA.add hB)
  have hden : Continuous (fun t : ℝ =>
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) :=
    Complex.continuous_normSq.comp hB
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
  exact hnum.div hden (fun t =>
    (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_normSq_pos
      W hp t).ne')

private theorem continuous_pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    Continuous (pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p) := by
  have hA := continuous_pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    hε W (X := X) hp
  have hB := continuous_pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W hp
  have hnum : Continuous (fun t : ℝ =>
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
          pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) :=
    Complex.continuous_normSq.comp (hA.sub hB)
  have hden : Continuous (fun t : ℝ =>
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) :=
    Complex.continuous_normSq.comp hB
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
  exact hnum.div hden (fun t =>
    (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_normSq_pos
      W hp t).ne')

private theorem intervalIntegrable_pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p)
      volume 0 W.rectangle.T :=
  (continuous_pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity hε W (X := X) hp).intervalIntegrable
    (μ := volume) 0 W.rectangle.T

private theorem intervalIntegrable_pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p)
      volume 0 W.rectangle.T :=
  (continuous_pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity hε W (X := X) hp).intervalIntegrable
    (μ := volume) 0 W.rectangle.T

private theorem intervalIntegrable_pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    IntervalIntegrable
      (fun t =>
        (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re)
      volume 0 W.rectangle.T := by
  have hA := continuous_pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    hε W (X := X) hp
  have hB := continuous_pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W hp
  have hq : ∀ t : ℝ,
      pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t ≠ 0 := by
    intro t
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  have hdiv : Continuous
      (fun t => pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t /
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) :=
    hA.div hB hq
  have hre : Continuous
      (fun t =>
        (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re) := by
    convert Complex.continuous_re.comp hdiv using 1
    funext t
    rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div W hp t]
    rfl
  exact hre.intervalIntegrable (μ := volume) 0 W.rectangle.T

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayKernel_eq_energy_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    4 * pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p =
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p -
        pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p := by
  have hplus := intervalIntegrable_pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
    hε W (X := X) hp
  have hminus := intervalIntegrable_pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
    hε W (X := X) hp
  have hamp := intervalIntegrable_pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re
    hε W (X := X) hp
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy
  rw [← pascalCenteredXiPrimeSideFinitePrimePowerRayComplexKernel_eq_rayKernel hε W hp]
  unfold pascalCenteredXiPrimeSideFinitePrimePowerRayComplexKernel
  rw [← intervalIntegral.integral_sub hplus hminus]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  exact pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_eq_normalized_density_difference
    W hp t

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy_nonneg
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    0 ≤ pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy
  exact intervalIntegral.integral_nonneg_of_ae W.rectangle.hT.le
    (Filter.Eventually.of_forall
      (pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity_nonneg ε W hp))

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy_nonneg
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    0 ≤ pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy
  exact intervalIntegral.integral_nonneg_of_ae W.rectangle.hT.le
    (Filter.Eventually.of_forall
      (pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_nonneg ε W hp))

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayKernel_nonneg_iff_energy_order
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    0 ≤ pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p ↔
      pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p ≤
        pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p := by
  have henergy := pascalCenteredXiPrimeSideFinitePrimePowerRayKernel_eq_energy_difference
    hε W (X := X) hp
  constructor <;> intro h <;> nlinarith [henergy]

/-! ## CS17-E: finite aggregate prime-weighted energies -/

noncomputable def pascalCenteredXiPrimeSideAggregateRayPlusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    Real.log (p : ℝ) *
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p

noncomputable def pascalCenteredXiPrimeSideAggregateRayMinusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    Real.log (p : ℝ) *
      pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p

theorem real_log_prime_coordinate_nonneg
    {X p : ℕ} (hp : p ∈ pascalPrimeCoordinateSupportUpTo X) :
    0 ≤ Real.log (p : ℝ) := by
  have hprime := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1
  exact (Real.log_pos (by exact_mod_cast hprime.one_lt)).le

theorem pascalCenteredXiPrimeSideAggregateRayPlusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X := by
  classical
  unfold pascalCenteredXiPrimeSideAggregateRayPlusEnergy
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (real_log_prime_coordinate_nonneg hp)
    (pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy_nonneg
      hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1)

theorem pascalCenteredXiPrimeSideAggregateRayMinusEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X := by
  classical
  unfold pascalCenteredXiPrimeSideAggregateRayMinusEnergy
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (real_log_prime_coordinate_nonneg hp)
    (pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy_nonneg
      hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1)

theorem pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    4 * (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
      pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X -
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X := by
  classical
  rw [pascalCenteredXiPrimeSideFiniteModeSum_eq_primePowerRays hε W X]
  unfold pascalCenteredXiPrimeSideAggregateRayPlusEnergy
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
        4 * (Real.log (x : ℝ) *
          pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X x)) =
      ∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (x : ℝ) *
          (4 * pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X x) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
    _ = ∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (x : ℝ) *
          (pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X x -
            pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X x) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [pascalCenteredXiPrimeSideFinitePrimePowerRayKernel_eq_energy_difference
            hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1]
    _ = (∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
          Real.log (x : ℝ) *
            pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X x) -
        (∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
          Real.log (x : ℝ) *
            pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X x) := by
          calc
            (∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
                Real.log (x : ℝ) *
                  (pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X x -
                    pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X x)) =
              ∑ x ∈ pascalPrimeCoordinateSupportUpTo X,
                (Real.log (x : ℝ) *
                    pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X x -
                  Real.log (x : ℝ) *
                    pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X x) := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  ring
            _ = _ := by rw [Finset.sum_sub_distrib]

theorem pascalCenteredXiPrimeSideFiniteModeSum_nonneg_iff_aggregateRayEnergy_order
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) ↔
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X := by
  have hledger := pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference
    hε W X
  constructor <;> intro h <;> nlinarith [hledger]

/-! ## CS17-F: finite block compatibility -/

theorem pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_aggregateRayEnergy_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    4 * pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X Y =
      (pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W Y -
          pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X) -
        (pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W Y -
          pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X) := by
  have hblock := pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_mode_sum_difference
    hε W X Y
  have hY := pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference
    hε W Y
  have hX := pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference
    hε W X
  nlinarith [hblock, hY, hX]

/-! ## CS17-G: aggregate ordering frontier -/

theorem pascalCenteredXiPrimeSideFiniteModeSum_nonneg_iff_aggregate_energy_order
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) ↔
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X :=
  pascalCenteredXiPrimeSideFiniteModeSum_nonneg_iff_aggregateRayEnergy_order hε W X

inductive PascalCenteredXiPrimeSideAggregateRayEnergyOrderingGap : Prop
  | noIndependentAggregateRayEnergyOrderingProvider

end DkMath.RH.CFBRCProjection
