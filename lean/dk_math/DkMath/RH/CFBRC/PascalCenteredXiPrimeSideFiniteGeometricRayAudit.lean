/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSidePrimePowerRayAudit
import Mathlib.Tactic

/-!
# CS15: finite geometric compression of one prime-power ray

This module keeps the CS14 cutoff finite and exposes the corresponding
complex source before real projection and interval integration.  The
geometric compression is denominator-free and finite.  No infinite ray,
integral exchange, sign provider, or RH consequence is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped Interval Topology

/-! ## CS15-A: finite exponent support -/

/-- The zero-based exponent indices carried by one base-prime ray. -/
def pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo
    (X p : ℕ) : Finset ℕ :=
  (Finset.range X).filter (fun k => p ^ (k + 1) ≤ X)

@[simp] theorem mem_pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_iff
    {X p k : ℕ} :
    k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p ↔
      k < X ∧ p ^ (k + 1) ≤ X := by
  simp [pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo]

theorem pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_subset_range
    (X p : ℕ) :
    pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p ⊆ Finset.range X := by
  intro k hk
  exact Finset.mem_range.mpr
    (mem_pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_iff.mp hk).1

theorem pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_pos
    {X p k : ℕ}
    (_hk : k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p) :
    0 < k + 1 := by
  omega

theorem pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_downward
    {X p k l : ℕ} (hp : Nat.Prime p)
    (hl : l ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p)
    (hkl : k ≤ l) :
    k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p := by
  have hl' := mem_pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_iff.mp hl
  apply mem_pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_iff.mpr
  constructor
  · exact lt_of_le_of_lt hkl hl'.1
  · exact (Nat.pow_le_pow_right (Nat.le_of_lt hp.one_lt)
      (Nat.add_le_add_right hkl 1)).trans hl'.2

/-! ## CS15-B: one-step ratio and prime-power transport -/

/-- The one-step complex ratio on a fixed base-prime ray. -/
noncomputable def pascalCenteredXiPrimeSidePrimeRatio
    (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (-s)

theorem pascalCenteredXiPrimeSidePrimePowerMode_eq_ratio_pow
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    (((p ^ j : ℕ) : ℂ) ^ (-s)) =
      pascalCenteredXiPrimeSidePrimeRatio p s ^ j := by
  rw [← eulerPrimePowerMode_eq_primePower_cpow_neg hp s]
  simp [eulerPrimePowerMode, pascalCenteredXiPrimeSidePrimeRatio,
    eulerPrimePrimitiveMode_eq_cpow_neg hp]

theorem pascalCenteredXiPrimeSidePrimePowerMode_eq_ratio_succ
    {p k : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    (((p ^ (k + 1) : ℕ) : ℂ) ^ (-s)) =
      pascalCenteredXiPrimeSidePrimeRatio p s ^ (k + 1) :=
  pascalCenteredXiPrimeSidePrimePowerMode_eq_ratio_pow hp s

/-! ## CS15-C: source-level finite ray amplitude -/

noncomputable def pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    (((p ^ (k + 1) : ℕ) : ℂ) ^
      (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))

/-- The finite complex ray before `Complex.re` and interval integration. -/
noncomputable def pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t

noncomputable def pascalCenteredXiPrimeSideFinitePrimePowerRayComplexKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re

private theorem continuous_pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {p k : ℕ}
    (hp : Nat.Prime p) :
    Continuous (pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k) := by
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
  have hpow : Continuous (fun t : ℝ =>
      (((p ^ (k + 1) : ℕ) : ℂ) ^
        (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) := by
    let : NeZero ((p ^ (k + 1) : ℕ) : ℂ) :=
      ⟨by exact_mod_cast (pow_ne_zero (k + 1) hp.ne_zero)⟩
    exact (continuous_const_cpow (((p ^ (k + 1) : ℕ) : ℂ))).comp
      (continuous_neg.comp hpath)
  exact hweight.mul hpow

private theorem intervalIntegrable_pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {p k : ℕ}
    (hp : Nat.Prime p) :
    IntervalIntegrable
      (fun t =>
        (pascalCenteredXiPrimeSideFinitePrimePowerRaySummand ε W p k t).re)
      volume 0 W.rectangle.T :=
  (Complex.continuous_re.comp
      (continuous_pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
        hε W hp)).intervalIntegrable (μ := volume) 0 W.rectangle.T

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_weight_mul_ratio_core
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
          pascalCenteredXiPrimeSidePrimeRatio p
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) ^ (k + 1) := by
  unfold pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
  apply Finset.sum_congr rfl
  intro k hk
  rw [pascalCenteredXiPrimeSidePrimePowerMode_eq_ratio_succ hp]

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayComplexKernel_eq_rayKernel
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayComplexKernel ε W X p =
      pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p := by
  unfold pascalCenteredXiPrimeSideFinitePrimePowerRayComplexKernel
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
    pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
    pascalCenteredXiPrimeSideFinitePrimePowerRayKernel
    pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo
  simp only [Complex.re_sum]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hcut : p ^ (k + 1) ≤ X
    · simp only [hcut, if_pos, pascalCenteredXiPrimeSideFiniteModeKernel]
      congr 1
      funext t
      have hpow : p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hp.ne_zero
      simp [pascalCenteredXiPrimeSideFiniteModeIntegrand,
        pascalCenteredXiPrimeSideModePhaseNode, hp.ne_zero]
    · simp [hcut]
  · intro k hk
    exact intervalIntegrable_pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
      hε W hp

/-! ## CS15-D: denominator-free finite geometric compression -/

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayCore
    (q : ℂ) (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.range m, q ^ (k + 1)

theorem pascalCenteredXiPrimeSideFiniteGeometricRayCore_compression
    (q : ℂ) (m : ℕ) :
    (1 - q) * pascalCenteredXiPrimeSideFiniteGeometricRayCore q m =
      q - q ^ (m + 1) := by
  induction m with
  | zero => simp [pascalCenteredXiPrimeSideFiniteGeometricRayCore]
  | succ m ih =>
      have hcore : pascalCenteredXiPrimeSideFiniteGeometricRayCore q (m + 1) =
          pascalCenteredXiPrimeSideFiniteGeometricRayCore q m + q ^ (m + 1) := by
        simp [pascalCenteredXiPrimeSideFiniteGeometricRayCore,
          Finset.sum_range_succ]
      rw [hcore]
      calc
        (1 - q) *
            (pascalCenteredXiPrimeSideFiniteGeometricRayCore q m + q ^ (m + 1)) =
            (1 - q) * pascalCenteredXiPrimeSideFiniteGeometricRayCore q m +
              (1 - q) * q ^ (m + 1) := by ring
        _ = (q - q ^ (m + 1)) + (1 - q) * q ^ (m + 1) := by rw [ih]
        _ = q - q ^ (m + 1 + 1) := by
          have hpow : q ^ (m + 1 + 1) = q ^ (m + 1) * q := by
            rw [pow_succ]
          rw [hpow]
          ring

theorem pascalCenteredXiPrimeSideFiniteGeometricRayCore_compression_at_prime
    {p : ℕ} (_hp : Nat.Prime p) (s : ℂ) (m : ℕ) :
    (1 - pascalCenteredXiPrimeSidePrimeRatio p s) *
        pascalCenteredXiPrimeSideFiniteGeometricRayCore
          (pascalCenteredXiPrimeSidePrimeRatio p s) m =
      pascalCenteredXiPrimeSidePrimeRatio p s -
        pascalCenteredXiPrimeSidePrimeRatio p s ^ (m + 1) :=
  pascalCenteredXiPrimeSideFiniteGeometricRayCore_compression _ _

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayCore_eq_geometricCore_of_support_eq_range
    {X p m : ℕ} (hsupport :
      pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p =
        Finset.range m) (q : ℂ) :
    (∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
      q ^ (k + 1)) =
      pascalCenteredXiPrimeSideFiniteGeometricRayCore q m := by
  rw [hsupport]
  rfl

/-! ## CS15-F: phase-lattice compatibility -/

theorem pascalCenteredXiPrimeSideFiniteGeometricRayCore_succ
    (q : ℂ) (m : ℕ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayCore q (m + 1) =
      pascalCenteredXiPrimeSideFiniteGeometricRayCore q m + q ^ (m + 1) := by
  simp [pascalCenteredXiPrimeSideFiniteGeometricRayCore, Finset.sum_range_succ]

theorem pascalCenteredXiPrimeSidePrimeRatio_mul_primePowerMode_eq_next
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    pascalCenteredXiPrimeSidePrimeRatio p s *
        (((p ^ j : ℕ) : ℂ) ^ (-s)) =
      (((p ^ (j + 1) : ℕ) : ℂ) ^ (-s)) := by
  rw [pascalCenteredXiPrimeSidePrimePowerMode_eq_ratio_pow hp s,
    pascalCenteredXiPrimeSidePrimePowerMode_eq_ratio_pow hp s]
  simp [pow_succ, mul_comm]

theorem pascalCenteredXiPrimeSideFiniteGeometricRay_phase_spacing
    {ε : ℝ} {p j : ℕ} (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSidePrimePowerPhasePlus ε p (j + 1) -
        pascalCenteredXiPrimeSidePrimePowerPhasePlus ε p j =
      -Real.log (p : ℝ) ∧
    pascalCenteredXiPrimeSidePrimePowerPhaseMinus ε p (j + 1) -
        pascalCenteredXiPrimeSidePrimePowerPhaseMinus ε p j =
      -Real.log (p : ℝ) :=
  pascalCenteredXiPrimeSidePrimePowerPhase_spacing hp

/- The finite source is compressed, but no signed-ray conclusion is supplied. -/
inductive PascalCenteredXiPrimeSideFiniteGeometricRayGap : Prop
  | signedRayCancellationProviderPending

end DkMath.RH.CFBRCProjection
