/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideModeKernelPhaseAudit
import Mathlib.Tactic

/-!
# CS14: canonical prime-power ray audit

This module reindexes the already finite CS12 mode ledger through the
repository's canonical prime-power support and groups it by base prime.  The
result is an exact finite algebraic rewrite.  It is not a sign theorem, an
infinite-series rearrangement, or a prime-power/integral exchange.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet

/-! ## CS14-A/B: canonical support and pair support -/

theorem pascalCenteredXiPrimeSideFiniteModeSum_eq_canonicalPrimePowerSupport
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
    ∑ q ∈ canonicalPrimePowerSupportUpTo X,
      canonicalPrimePowerShadowCost q *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W q := by
  classical
  unfold canonicalPrimePowerSupportUpTo
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqpp : IsPrimePowerLabel q
  · rw [canonicalPrimePowerShadowCost_eq_vonMangoldt q]
    simp [hqpp]
  · have hzero : ArithmeticFunction.vonMangoldt q = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      exact (isPrimePowerLabel_iff_isPrimePow q).not.mp hqpp
    simp [hqpp, hzero]

theorem pascalCenteredXiPrimeSideCanonicalModeSum_eq_pairSupport
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
      canonicalPrimePowerShadowCost q *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W q) =
    ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
      Real.log (pk.1 : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W
          (pk.1 ^ (pk.2 + 1)) := by
  classical
  rw [← image_primePowerPairLabel_support_eq_canonicalSupport]
  symm
  apply Finset.sum_bij (fun pk _ => primePowerPairLabel pk)
  · intro pk hpk
    exact Finset.mem_image.mpr ⟨pk, hpk, rfl⟩
  · intro a ha b hb hab
    exact primePowerPairLabel_injOn X ha hb hab
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨pk, hpk, rfl⟩
    exact ⟨pk, hpk, rfl⟩
  · intro pk hpk
    have hsupport := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
    have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsupport.1).1
    rw [canonicalPrimePowerShadowCost_eq_log_of_witness hp (by omega)
      (q := primePowerPairLabel pk) (p := pk.1) (j := pk.2 + 1) rfl]
    rfl

/-! ## CS14-C: finite base-prime rays -/

/-- The finite positive-exponent ray of one base prime. -/
noncomputable def pascalCenteredXiPrimeSideFinitePrimePowerRayKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range X,
    if p ^ (k + 1) ≤ X then
      pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ (k + 1))
    else 0

theorem pascalCenteredXiPrimeSidePairSupportSum_eq_primePowerRays
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
      Real.log (pk.1 : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W
          (pk.1 ^ (pk.2 + 1))) =
    ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
      Real.log (p : ℝ) *
        pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p := by
  classical
  unfold pascalPrimePowerPairSupportUpTo
    pascalCenteredXiPrimeSideFinitePrimePowerRayKernel
  rw [Finset.sum_filter]
  calc
    (∑ a ∈ (pascalPrimeCoordinateSupportUpTo X).product (Finset.range X),
        if a.1 ^ (a.2 + 1) ≤ X then
          Real.log (a.1 : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeKernel ε W
              (a.1 ^ (a.2 + 1))
        else 0) =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        ∑ k ∈ Finset.range X,
          if p ^ (k + 1) ≤ X then
            Real.log (p : ℝ) *
              pascalCenteredXiPrimeSideFiniteModeKernel ε W
                (p ^ (k + 1))
          else 0 := by
        exact Finset.sum_product'
          (pascalPrimeCoordinateSupportUpTo X) (Finset.range X)
          (fun p k => if p ^ (k + 1) ≤ X then
            Real.log (p : ℝ) *
              pascalCenteredXiPrimeSideFiniteModeKernel ε W
                (p ^ (k + 1))
          else 0)
    _ = ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (p : ℝ) *
          ∑ k ∈ Finset.range X,
            if p ^ (k + 1) ≤ X then
              pascalCenteredXiPrimeSideFiniteModeKernel ε W
                (p ^ (k + 1))
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> ring

theorem pascalCenteredXiPrimeSideFiniteModeSum_eq_primePowerRays
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
    ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
      Real.log (p : ℝ) *
        pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p := by
  rw [pascalCenteredXiPrimeSideFiniteModeSum_eq_canonicalPrimePowerSupport
      hε W X,
    pascalCenteredXiPrimeSideCanonicalModeSum_eq_pairSupport hε W X,
    pascalCenteredXiPrimeSidePairSupportSum_eq_primePowerRays hε W X]

/-! ## CS14-D: phase lattice on one prime ray -/

theorem real_log_prime_pow_eq_mul
    {p j : ℕ} (_hp : Nat.Prime p) (_hj : 0 < j) :
    Real.log ((p ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log (p : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow]

noncomputable def pascalCenteredXiPrimeSidePrimePowerPhasePlus
    (ε : ℝ) (p j : ℕ) : ℝ :=
  ε - (j : ℝ) * Real.log (p : ℝ)

noncomputable def pascalCenteredXiPrimeSidePrimePowerPhaseMinus
    (ε : ℝ) (p j : ℕ) : ℝ :=
  -ε - (j : ℝ) * Real.log (p : ℝ)

theorem pascalCenteredXiPrimeSidePrimePowerPhasePlus_eq_naturalPhase
    {ε : ℝ} {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
        pascalCenteredXiPrimeSidePrimePowerPhasePlus ε p j =
      ε - Real.log ((p ^ j : ℕ) : ℝ) := by
  rw [pascalCenteredXiPrimeSidePrimePowerPhasePlus,
    real_log_prime_pow_eq_mul hp hj]

theorem pascalCenteredXiPrimeSidePrimePowerPhaseMinus_eq_naturalPhase
    {ε : ℝ} {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    pascalCenteredXiPrimeSidePrimePowerPhaseMinus ε p j =
      -ε - Real.log ((p ^ j : ℕ) : ℝ) := by
  rw [pascalCenteredXiPrimeSidePrimePowerPhaseMinus,
    real_log_prime_pow_eq_mul hp hj]

theorem pascalCenteredXiPrimeSidePrimePowerPhase_spacing
    {ε : ℝ} {p j : ℕ} (_hp : Nat.Prime p) :
    pascalCenteredXiPrimeSidePrimePowerPhasePlus ε p (j + 1) -
        pascalCenteredXiPrimeSidePrimePowerPhasePlus ε p j =
      -Real.log (p : ℝ) ∧
    pascalCenteredXiPrimeSidePrimePowerPhaseMinus ε p (j + 1) -
        pascalCenteredXiPrimeSidePrimePowerPhaseMinus ε p j =
      -Real.log (p : ℝ) := by
  constructor <;>
    simp [pascalCenteredXiPrimeSidePrimePowerPhasePlus,
      pascalCenteredXiPrimeSidePrimePowerPhaseMinus]
  <;> ring

/-! ## CS14-E/F: structural damping and finite geometric surface -/

theorem pascalCenteredXiPrimeSidePrimePowerMode_eq_natural_cpow
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j s =
      (((p ^ j : ℕ) : ℂ) ^ (-s)) :=
  eulerPrimePowerMode_eq_primePower_cpow_neg hp s

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayKernel_is_finite
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p =
      ∑ k ∈ Finset.range X,
        if p ^ (k + 1) ≤ X then
          pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ (k + 1))
        else 0 := by
  rfl

/- The ray rewrite exposes common positive `log p` coefficients, equal phase
spacing, and finite support only.  No ray sign or infinite geometric sum is
asserted here. -/
inductive PascalCenteredXiPrimeSidePrimePowerRayGap : Prop
  | rayCancellationProviderPending

end DkMath.RH.CFBRCProjection
