/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideNormalizedRayPolarizationOrderingAudit
import DkMath.CosmicFormula.Rotation.CF2D.Basic
import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import Mathlib.Tactic

/-!
# CS18: CF2D `q2` / `star` bridge for the finite prime-side polarization

This module translates the already-proved finite complex identities into the
existing CF2D algebra.  It is a structural bridge audit: no new ordering
provider, collision package, infinite exchange, endpoint sign theorem, or RH
conclusion is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.CosmicFormula.ThreeElement
open MeasureTheory
open scoped ComplexConjugate Interval Topology

/-! ## CS18-A: exact complex-to-CF2D coordinates -/

noncomputable def pascalCenteredXiPrimeSideComplexAsCF2DVec
    (z : ℂ) : Vec ℝ :=
  ⟨z.re, z.im⟩

@[simp]
theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_core (z : ℂ) :
    (pascalCenteredXiPrimeSideComplexAsCF2DVec z).core = z.re := rfl

@[simp]
theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_beam (z : ℂ) :
    (pascalCenteredXiPrimeSideComplexAsCF2DVec z).beam = z.im := rfl

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_q2 (z : ℂ) :
    Vec.q2 (pascalCenteredXiPrimeSideComplexAsCF2DVec z) =
      Complex.normSq z := by
  simp [pascalCenteredXiPrimeSideComplexAsCF2DVec, Vec.q2,
    Complex.normSq_apply]
  ring

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_conj (z : ℂ) :
    pascalCenteredXiPrimeSideComplexAsCF2DVec (conj z) =
      Vec.conj (pascalCenteredXiPrimeSideComplexAsCF2DVec z) := by
  simp [pascalCenteredXiPrimeSideComplexAsCF2DVec, Vec.conj]

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_zero :
    pascalCenteredXiPrimeSideComplexAsCF2DVec 0 = Vec.mk 0 0 := by
  rfl

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_one :
    pascalCenteredXiPrimeSideComplexAsCF2DVec 1 = Vec.mk 1 0 := by
  rfl

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_mul (z w : ℂ) :
    pascalCenteredXiPrimeSideComplexAsCF2DVec (z * w) =
      Vec.star
        (pascalCenteredXiPrimeSideComplexAsCF2DVec z)
        (pascalCenteredXiPrimeSideComplexAsCF2DVec w) := by
  simp [pascalCenteredXiPrimeSideComplexAsCF2DVec, Vec.star,
    Complex.mul_re, Complex.mul_im]

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_normSq_mul (z w : ℂ) :
    Complex.normSq (z * w) =
      Vec.q2 (Vec.star
        (pascalCenteredXiPrimeSideComplexAsCF2DVec z)
        (pascalCenteredXiPrimeSideComplexAsCF2DVec w)) := by
  rw [← pascalCenteredXiPrimeSideComplexAsCF2DVec_q2 (z * w),
    pascalCenteredXiPrimeSideComplexAsCF2DVec_mul]

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_normSq_mul_factorization
    (z w : ℂ) :
    Complex.normSq (z * w) =
      Complex.normSq z * Complex.normSq w := by
  rw [← pascalCenteredXiPrimeSideComplexAsCF2DVec_q2 (z * w),
    pascalCenteredXiPrimeSideComplexAsCF2DVec_mul,
    Vec.q2_star,
    pascalCenteredXiPrimeSideComplexAsCF2DVec_q2,
    pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]

/-! ## CS18-B: CS17 polarization as literal q2 polarization -/

theorem pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_q2_polarization
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    4 * pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t =
      Vec.q2
          (pascalCenteredXiPrimeSideComplexAsCF2DVec
            (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
              pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) -
        Vec.q2
          (pascalCenteredXiPrimeSideComplexAsCF2DVec
            (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
              pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) := by
  rw [pascalCenteredXiPrimeSideComplexAsCF2DVec_q2,
    pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]
  exact pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_polarization
    ε W X p t

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity_eq_q2_ratio
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t =
      Vec.q2
          (pascalCenteredXiPrimeSideComplexAsCF2DVec
            (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
              pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) /
        Vec.q2
          (pascalCenteredXiPrimeSideComplexAsCF2DVec
            (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) := by
  rw [pascalCenteredXiPrimeSideComplexAsCF2DVec_q2,
    pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]
  rfl

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_eq_q2_ratio
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t =
      Vec.q2
          (pascalCenteredXiPrimeSideComplexAsCF2DVec
            (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
              pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) /
        Vec.q2
          (pascalCenteredXiPrimeSideComplexAsCF2DVec
            (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) := by
  rw [pascalCenteredXiPrimeSideComplexAsCF2DVec_q2,
    pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]
  rfl

/-! ## CS18-C: normalized quotient ray state -/

noncomputable def pascalCenteredXiPrimeSideNormalizedRayState
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t

theorem pascalCenteredXiPrimeSideNormalizedRayState_eq_endpoint_div
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideNormalizedRayState ε W X p t =
      pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t /
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t := by
  exact pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div W hp t

private theorem complex_add_one_div_eq_add_div
    {z w : ℂ} (hw : w ≠ 0) :
    z / w + 1 = (z + w) / w := by
  field_simp [hw]

private theorem complex_sub_one_div_eq_sub_div
    {z w : ℂ} (hw : w ≠ 0) :
    z / w - 1 = (z - w) / w := by
  field_simp [hw]

theorem pascalCenteredXiPrimeSideNormalizedRayState_plus_one_q2
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    Vec.q2
        (pascalCenteredXiPrimeSideComplexAsCF2DVec
          (pascalCenteredXiPrimeSideNormalizedRayState ε W X p t + 1)) =
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t := by
  let A := pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t
  let B := pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t
  have hB : B ≠ 0 := by
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  have hstate := pascalCenteredXiPrimeSideNormalizedRayState_eq_endpoint_div
    (ε := ε) W (X := X) hp t
  rw [pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]
  rw [hstate]
  rw [complex_add_one_div_eq_add_div hB, Complex.normSq_div]
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
  rfl

theorem pascalCenteredXiPrimeSideNormalizedRayState_minus_one_q2
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    Vec.q2
        (pascalCenteredXiPrimeSideComplexAsCF2DVec
          (pascalCenteredXiPrimeSideNormalizedRayState ε W X p t - 1)) =
      pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t := by
  let A := pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t
  let B := pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t
  have hB : B ≠ 0 := by
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  have hstate := pascalCenteredXiPrimeSideNormalizedRayState_eq_endpoint_div
    (ε := ε) W (X := X) hp t
  rw [pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]
  rw [hstate]
  rw [complex_sub_one_div_eq_sub_div hB, Complex.normSq_div]
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
  rfl

theorem pascalCenteredXiPrimeSideNormalizedRayState_energy_order_iff_re_nonneg
    (z : ℂ) :
    Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) ↔
      0 ≤ z.re := by
  norm_num [Complex.normSq_apply]
  constructor <;> intro h <;> linarith

/-! ## CS18-D: two-channel ThreeElement interpretation -/

noncomputable def pascalCenteredXiPrimeSideRealChannelState
    (A B : ℂ) : Vec ℝ :=
  ⟨A.re, B.re⟩

noncomputable def pascalCenteredXiPrimeSideImagChannelState
    (A B : ℂ) : Vec ℝ :=
  ⟨A.im, B.im⟩

theorem pascalCenteredXiPrimeSideTwoChannel_plusWhole_eq_normSq_add
    (A B : ℂ) :
    cf2dPlusWhole (pascalCenteredXiPrimeSideRealChannelState A B) +
        cf2dPlusWhole (pascalCenteredXiPrimeSideImagChannelState A B) =
      Complex.normSq (A + B) := by
  simp [pascalCenteredXiPrimeSideRealChannelState,
    pascalCenteredXiPrimeSideImagChannelState, cf2dPlusWhole,
    plusWhole, Complex.normSq_apply]
  ring

theorem pascalCenteredXiPrimeSideTwoChannel_minusWhole_eq_normSq_sub
    (A B : ℂ) :
    cf2dMinusWhole (pascalCenteredXiPrimeSideRealChannelState A B) +
        cf2dMinusWhole (pascalCenteredXiPrimeSideImagChannelState A B) =
      Complex.normSq (A - B) := by
  simp [pascalCenteredXiPrimeSideRealChannelState,
    pascalCenteredXiPrimeSideImagChannelState, cf2dMinusWhole,
    minusWhole, Complex.normSq_apply]
  ring

theorem pascalCenteredXiPrimeSideTwoChannel_interactionBeam_eq_two_re_mul_conj
    (A B : ℂ) :
    cf2dInteractionBeam (pascalCenteredXiPrimeSideRealChannelState A B) +
        cf2dInteractionBeam (pascalCenteredXiPrimeSideImagChannelState A B) =
      2 * Complex.re (A * conj B) := by
  simp [pascalCenteredXiPrimeSideRealChannelState,
    pascalCenteredXiPrimeSideImagChannelState, cf2dInteractionBeam,
    interactionBeam, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem pascalCenteredXiPrimeSideTwoChannel_polarization
    (A B : ℂ) :
    (cf2dPlusWhole (pascalCenteredXiPrimeSideRealChannelState A B) +
        cf2dPlusWhole (pascalCenteredXiPrimeSideImagChannelState A B)) -
      (cf2dMinusWhole (pascalCenteredXiPrimeSideRealChannelState A B) +
        cf2dMinusWhole (pascalCenteredXiPrimeSideImagChannelState A B)) =
      4 * Complex.re (A * conj B) := by
  rw [pascalCenteredXiPrimeSideTwoChannel_plusWhole_eq_normSq_add,
    pascalCenteredXiPrimeSideTwoChannel_minusWhole_eq_normSq_sub]
  exact (complex_four_mul_re_mul_conj_eq_normSq_add_sub_normSq_sub A B).symm

/-! ## CS18-E: finite complex powers as repeated `Vec.star` -/

def pascalCenteredXiPrimeSideCF2DStarPower
    (v : Vec ℝ) : ℕ → Vec ℝ
  | 0 => Vec.one ℝ
  | n + 1 => Vec.star (pascalCenteredXiPrimeSideCF2DStarPower v n) v

theorem pascalCenteredXiPrimeSideComplexAsCF2DVec_pow_eq_starPower
    (z : ℂ) (n : ℕ) :
    pascalCenteredXiPrimeSideComplexAsCF2DVec (z ^ n) =
      pascalCenteredXiPrimeSideCF2DStarPower
        (pascalCenteredXiPrimeSideComplexAsCF2DVec z) n := by
  induction n with
  | zero => simp [pascalCenteredXiPrimeSideComplexAsCF2DVec,
      pascalCenteredXiPrimeSideCF2DStarPower, Vec.one]
  | succ n ih =>
      rw [pow_succ, pascalCenteredXiPrimeSideComplexAsCF2DVec_mul, ih]
      rfl

/-! ## CS18-F: q2 energy ledger -/

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Density
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℝ :=
  Vec.q2
      (pascalCenteredXiPrimeSideComplexAsCF2DVec
        (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t +
          pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) /
    Vec.q2
      (pascalCenteredXiPrimeSideComplexAsCF2DVec
        (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t))

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Density
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℝ :=
  Vec.q2
      (pascalCenteredXiPrimeSideComplexAsCF2DVec
        (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t -
          pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) /
    Vec.q2
      (pascalCenteredXiPrimeSideComplexAsCF2DVec
        (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t))

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Density_eq_plusDensity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Density ε W X p t =
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t := by
  exact (pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity_eq_q2_ratio
    ε W X p t).symm

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Density_eq_minusDensity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Density ε W X p t =
      pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t := by
  exact (pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_eq_q2_ratio
    ε W X p t).symm

theorem pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_q2_pos
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    0 < Vec.q2
      (pascalCenteredXiPrimeSideComplexAsCF2DVec
        (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t)) := by
  rw [pascalCenteredXiPrimeSideComplexAsCF2DVec_q2]
  exact pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector_normSq_pos W hp t

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Energy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Density ε W X p t

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Energy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Density ε W X p t

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Energy_eq_plusEnergy
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (_hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Energy ε W X p =
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Energy
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  exact pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Density_eq_plusDensity
    ε W X p t

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Energy_eq_minusEnergy
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (_hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Energy ε W X p =
      pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Energy
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  exact pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Density_eq_minusDensity
    ε W X p t

noncomputable def pascalCenteredXiPrimeSideAggregateRayPlusQ2Energy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    Real.log (p : ℝ) *
      pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Energy ε W X p

noncomputable def pascalCenteredXiPrimeSideAggregateRayMinusQ2Energy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    Real.log (p : ℝ) *
      pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Energy ε W X p

theorem pascalCenteredXiPrimeSideAggregateRayPlusQ2Energy_eq_plusEnergy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayPlusQ2Energy ε W X =
      pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X := by
  classical
  unfold pascalCenteredXiPrimeSideAggregateRayPlusQ2Energy
    pascalCenteredXiPrimeSideAggregateRayPlusEnergy
  apply Finset.sum_congr rfl
  intro p hp
  rw [pascalCenteredXiPrimeSideFiniteGeometricRayPlusQ2Energy_eq_plusEnergy
    hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1]

theorem pascalCenteredXiPrimeSideAggregateRayMinusQ2Energy_eq_minusEnergy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayMinusQ2Energy ε W X =
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X := by
  classical
  unfold pascalCenteredXiPrimeSideAggregateRayMinusQ2Energy
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy
  apply Finset.sum_congr rfl
  intro p hp
  rw [pascalCenteredXiPrimeSideFiniteGeometricRayMinusQ2Energy_eq_minusEnergy
    hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1]

theorem pascalCenteredXiPrimeSideAggregateRayQ2Energy_order_iff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayMinusQ2Energy ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayPlusQ2Energy ε W X ↔
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X := by
  rw [pascalCenteredXiPrimeSideAggregateRayMinusQ2Energy_eq_minusEnergy hε W X,
    pascalCenteredXiPrimeSideAggregateRayPlusQ2Energy_eq_plusEnergy hε W X]

/-! ## CS18-G: collision applicability audit -/

/- The two-channel CF2D flow vocabulary is available, but CS18 supplies no
single filter, common target, same-object assimilation limits, or independent
nonzero-target certificate for the prime-side finite ordering problem. -/
inductive PascalCenteredXiPrimeSideCF2DCollisionBridgeGap : Prop
  | noSourceDerivedSameObjectAssimilationPackage

end DkMath.RH.CFBRCProjection
